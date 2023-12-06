#include "internal.hpp"
#include "unordered_set"

namespace CaDiCaL {


/*------------------------------------------------------------------------*/

// Enable proof drupping.

void Internal::drup () {
  assert (!drupper);
  drupper = new Drupper (this);
}

/*------------------------------------------------------------------------*/

DrupperClause::DrupperClause (bool deletion, bool failing)
:
  revive_at (0), deleted (deletion)
{
  variant = CLAUSE;
  counterpart = 0;
};

DrupperClause::DrupperClause (vector<int> c, bool deletion, bool failing)
:
  revive_at (0), deleted (deletion)
{
  assert (c.size ());
  variant = LITERALS;
  new (&literals) std::vector<int>(c);
};

DrupperClause::DrupperClause (Clause * c, bool deletion, bool failing)
:
  revive_at (0), deleted (deletion)
{
  assert (c && c->size);
  variant = LITERALS;
  new (&literals) std::vector<int>();
  for (int l : *c)
    literals.push_back (l);
};

DrupperClause::~DrupperClause () {
  destroy_variant ();
}

DCVariant DrupperClause::variant_type () const {
  return variant ? LITERALS : CLAUSE;
}

void DrupperClause::destroy_variant () {
  if (variant_type () == CLAUSE)
    counterpart = 0;
  else
    literals.~vector();
}

void DrupperClause::set_variant (Clause * c) {
  destroy_variant ();
  variant = CLAUSE;
  counterpart = c;
}

void DrupperClause::set_variant (const vector<int> & c) {
  destroy_variant ();
  variant = LITERALS;
  new (&literals) std::vector<int>(c);
  literals = c;
}

Clause * DrupperClause::flip_variant () {
  assert (variant_type () == CLAUSE);
  Clause * ref = counterpart;
  assert (ref);
  destroy_variant ();
  set_variant (vector<int> ());
  for (int l : *ref)
    literals.push_back (l);
  return ref;
}

Clause * DrupperClause::clause () {
  assert (variant_type () == CLAUSE);
  return counterpart;
}

vector<int> & DrupperClause::lits () {
  assert (variant_type () == LITERALS);
  return literals;
}

const vector<int> & DrupperClause::lits () const {
  assert (variant_type () == LITERALS);
  return literals;
}

/*------------------------------------------------------------------------*/

Drupper::Drupper (Internal * i, File * f)
:
  internal (i), failed_constraint (0),
  isolated (0), validating (0), file (f)
{
  LOG ("DRUPPER new");

  setup_internal_options ();

  // Initialize statistics.
  //
  memset (&stats, 0, sizeof (stats));

  if (internal->opts.drupdumpcore && !f)
    file = File::write (internal, stdout, "<stdout>");
}

Drupper::~Drupper () {
  LOG ("DRUPPER delete");
  isolated = true;
  for (const auto & dc : proof)
    delete (DrupperClause *) dc;
  for (const auto & c : unit_clauses)
    delete [] (char*) c;
  for (const auto & c : clauses)
    delete [] (char*) c;
  delete file;
}
/*------------------------------------------------------------------------*/

void Drupper::set (const char * setting, bool val) {
  if (!strcmp (setting, "core_units"))
    settings.core_units = val;
  else if (!strcmp (setting, "reconstruct"))
    settings.reconstruct = val;
  else if (!strcmp (setting, "core_first"))
    settings.core_first = val;
  else if (!strcmp (setting, "check_core"))
    settings.check_core = val;
  else if (!strcmp (setting, "extract_core_literals"))
    settings.extract_core_literals = val;
  else assert (0 && "unknown drupper seting");
}

bool Drupper::setup_internal_options () {
  auto & opts = internal->opts;
  bool updated = false;
  updated |= opts.chrono;
  updated |= opts.probe;
  updated |= opts.compact;
  updated |= opts.vivify;
  opts.chrono = 0;
  opts.probe = 0;
  opts.compact = 0;
  ///FIXME: ../interesting/vivify/red-*
  opts.vivify = 0;
  return updated;
}

/*------------------------------------------------------------------------*/

Clause * Drupper::new_clause (const vector<int> & clause) {

  assert (clause.size () <= (size_t) INT_MAX);
  const int size = (int) clause.size ();
  assert (size >= 2);

  // Determine whether this clauses should be kept all the time.
  //
  bool keep = true;

  size_t bytes = Clause::bytes (size);
  Clause * c = (Clause *) new char[bytes];

  c->conditioned = false;
  c->covered = false;
  c->enqueued = false;
  c->frozen = false;
  c->garbage = false;
  c->gate = false;
  c->hyper = false;
  c->instantiated = false;
  c->keep = keep;
  c->moved = false;
  c->reason = false;
  c->redundant = true;
  c->transred = false;
  c->subsume = false;
  c->vivified = false;
  c->vivify = false;
  c->core = false;
  c->drup_idx = 0;
  c->used = 0;

  c->glue = 0;
  c->size = size;
  c->pos = 2;

  for (int i = 0; i < size; i++) c->literals[i] = clause[i];

  // Just checking that we did not mess up our sophisticated memory layout.
  // This might be compiler dependent though. Crucial for correctness.
  //
  assert (c->bytes () == bytes);

  clauses.push_back (c);

  return c;
}

Clause * Drupper::new_unit_clause (const int lit, bool original) {

  const int size = 1;

  size_t bytes = Clause::bytes (size);
  Clause * c = (Clause *) new char[bytes];

  stats.units++;

  c->conditioned = false;
  c->covered = false;
  c->enqueued = false;
  c->frozen = false;
  c->garbage = false;
  c->gate = false;
  c->hyper = false;
  c->instantiated = false;
  c->keep = true;
  c->moved = false;
  c->reason = false;
  ///NOTE: for clauses of size 1, irredundant iff original.
  c->redundant = !original;
  c->transred = false;
  c->subsume = false;
  c->vivified = false;
  c->vivify = false;
  c->core = false;
  c->drup_idx = 0;
  c->used = c->glue = 0;
  c->size = size;
  c->pos = 2;
  c->literals[0] = lit;

  assert (c->bytes () == bytes);

  unit_clauses.push_back (c);
  LOG (c, "new pointer %p", (void*) c);

  return c;
}

/*------------------------------------------------------------------------*/

void Drupper::set_counterpart (DrupperClause * dc, Clause * c) {
  assert (dc->variant_type () == LITERALS || !dc->clause ());
  if (c)
    dc->set_variant (c);
  else {
    assert (dc->variant_type () == LITERALS && dc->lits().size ());
  }
  stats.counterparts++;
}

void Drupper::reset_counterpart (DrupperClause * dc) {
  Clause * counterpart = dc->flip_variant ();
  counterpart->drup_idx = 0;
  stats.counterparts--;
}

/*------------------------------------------------------------------------*/

// Return true iff the clause contains a literal and its negation.
bool Drupper::trivially_satisfied (const vector <int> & c) {
  struct {
    bool operator () (const int & a, const int & b) {
      return (abs (a) < abs (b)) || (abs (a) == abs (b) && a < b);
    }
  } sorter;
  auto sorted (c);
  std::sort (sorted.begin (), sorted.end (), sorter);
  for (unsigned i = 1; i < sorted.size (); i++)
    if (sorted[i] == -sorted[i-1])
      return true;
  return false;
}

///TODO: Consider using lazy drupper clause allocation: allocate once the internal
// clause is discarded from memory.
void Drupper::append_lemma (DrupperClause * dc, Clause * c) {
  assert (!dc->revive_at);
  if (dc->deleted) stats.deleted++;
  else stats.derived++;
  if (c) {
    if (dc->deleted) {
      if (c->drup_idx) {
        auto & pdc = proof[c->drup_idx - 1];
        assert (pdc->clause () == c);
        dc->revive_at = c->drup_idx;
        reset_counterpart (proof[c->drup_idx - 1]);
      }
    } else {
      c->drup_idx = proof.size () + 1;
    }
  }
  set_counterpart (dc, dc->deleted ? 0 : c);
  proof.push_back (dc);
}

void Drupper::append_failed (const vector<int> & c) {
  append_lemma (new DrupperClause (c), 0);
  append_lemma (new DrupperClause (c, true), 0);
  int i = proof.size () - 1;
  proof[i]->revive_at = i;
}

void Drupper::revive_clause (int i) {
  START (drup_revive);
  assert (i >= 0 && i < proof.size ());
  DrupperClause * dc = proof[i];
  assert (dc->deleted);
  const auto & literals = dc->lits ();
  assert (literals.size () > 1);
  for (int j : literals)
    if (internal->flags (j).eliminated ())
      internal->reactivate (j);
  Clause * c = new_clause (literals);
  internal->watch_clause (c);
  if (dc->revive_at) {
    int j = dc->revive_at - 1;
#ifndef NDEBUG
    assert (j < i && j >= 0);
    assert (!proof[j]->revive_at);  // Are chains even possible?
    assert (!proof[j]->deleted);
#endif
    set_counterpart (proof[j], c);
  }
  set_counterpart (proof[i], c);
  stats.revived++;
  STOP (drup_revive);
}

void Drupper::stagnate_clause (const int i) {
  Clause * c = proof[i]->clause ();
  {
    // See the discussion in 'propagate' on avoiding to eagerly trace binary
    // clauses as deleted (produce 'd ...' lines) as soon they are marked
    // garbage.
    assert (!c->garbage && "remove this if you are actually delaying the trace of garbage binaries");
  }
  assert (!c->moved);
  c->garbage = true;
  if (c->size > 1)
    internal->unwatch_clause (c);
}

///NOTE: The internal solver does not support reactivation
// of fixed literals. However, this is needed to be able
// to propagate these literals again.
void Drupper::reactivate_fixed (int l) {
  Flags & f = internal->flags (l);
  assert (f.status == Flags::FIXED);
  assert (internal->stats.now.fixed > 0);
  internal->stats.now.fixed--;
  f.status = Flags::ACTIVE;
  assert (internal->active (l));
  internal->stats.reactivated++;
  assert (internal->stats.inactive > 0);
  internal->stats.inactive--;
  internal->stats.active++;
}

/*------------------------------------------------------------------------*/

void Drupper::shrink_internal_trail (const unsigned trail_sz) {
  assert (trail_sz <= internal->trail.size());
  internal->trail.resize(trail_sz);
  internal->propagated = trail_sz;
  ///TODO: set internal->propagated2 properly.
  assert (!internal->level);
  assert(internal->control.size () == 1);
}

void Drupper::clean_conflict () {
  internal->unsat = false;
  internal->backtrack();
  internal->conflict = 0;
}

/*------------------------------------------------------------------------*/

void Drupper::undo_trail_literal (const int lit) {
  assert (internal->val (lit) > 0);
  if (!internal->active (lit))
    reactivate_fixed (lit);
  internal->unassign (lit);
  assert (!internal->val (lit));
  assert (internal->active (lit));
#ifndef NDEBUG
  Var & v = internal->var (lit);
  assert (v.reason);
  // v.reason = 0;
#endif
}

void Drupper::undo_trail_core (Clause * c, unsigned & trail_sz) {
  START (drup_undo_trail);
#ifndef NDEBUG
  assert (trail_sz > 0);
  assert (trail_sz <= internal->trail.size());
  assert (c && is_on_trail (c));
#endif

  int clit = c->literals[0];

#ifndef NDEBUG
  assert (internal->var (clit).reason == c);
  assert (internal->val (clit) > 0);
#endif

  while (internal->trail[--trail_sz] != clit)
  {
    assert(trail_sz > 0);
    int l = internal->trail[trail_sz];

    Clause * r = internal->var(l).reason;
    assert (r && r->literals[0] == l);

    undo_trail_literal (l);

    if (settings.core_units)
      mark_core (r);

    if (r->core)
      for (int j = 1; j < r->size; j++)
        mark_core (internal->var(r->literals[j]).reason);
  }

  assert(clit == internal->trail[trail_sz]);
  undo_trail_literal (clit);
  STOP (drup_undo_trail);
}


bool Drupper::is_on_trail (Clause * c) {
  assert (c);
  int lit = c->literals[0];
  return internal->val (lit) > 0 && internal->var (lit).reason == c;
}

/*------------------------------------------------------------------------*/

void Drupper::mark_core (Clause * c) {
  assert (c);
  if (!c->core) stats.core++;
  c->core = true;
}

void Drupper::mark_conflict_lit (const int l) {
  assert (internal->val(l) < 0);
  Var & v = internal->var(l);
  Clause * reason = v.reason;
  if (reason) mark_core (reason);
}

void Drupper::mark_conflict (bool overconstrained) {
  if (internal->unsat) {
    Clause * conflict = 0;
    if (overconstrained) {
      // Last deleted lemma is the falsified original.
      // Revive it and mark it as the conflict clause.
      int i = proof.size () - 1;
      assert (i >= 0 && proof[i]->deleted);
      DrupperClause * dc = proof[i];
      if (dc->lits ().size () == 1)
        set_counterpart (proof[i], new_unit_clause (dc->lits ()[0], false));
      else
        revive_clause (i);
      conflict = proof[i]->clause ();
    } else {
      conflict = internal->conflict;
    }
    mark_core (conflict);
    for (int lit : *conflict)
      mark_conflict_lit (lit);
  } else {
    if (internal->unsat_constraint && internal->constraint.size () > 1) {
      failed_constraint = new_clause (internal->constraint);
      mark_core (failed_constraint);
      internal->watch_clause (failed_constraint);
    }
    assert (!internal->marked_failed);
    internal->failing ();
    internal->marked_failed = true;
  }
}

void Drupper::mark_failing (const int proof_sz) {
  assert (proof_sz < proof.size () && !((proof.size () - proof_sz) % 2));
  for (int i = proof_sz; i < proof.size(); i++)
    if ((i - proof_sz) % 2)
      mark_core (proof[i]->clause ());
}

/*------------------------------------------------------------------------*/

void Drupper::assume_negation (const Clause * lemma) {
  assert (validating && !internal->level);
  assert (lemma && lemma->core);
  assert (internal->propagated == internal->trail.size ());

  vector <int> decisions;
  for (int lit : *lemma)
    if (!internal->val (lit))
      decisions.push_back (-lit);

  assert (decisions.size());
  internal->search_assume_multiple_decisions (decisions);
  assert (internal->level  == int (decisions.size()));
}

bool Drupper::propagate_conflict () {
  START (drup_propagate);
  assert(!internal->conflict);
  if (internal->propagate (settings.core_first))
  {
    START (drup_repropagate);
    {
      // If propagate fails, it may be due to incrementality and
      // missing units. re-propagate the entire trail.
      ///TODO: Understand what exactly happens and why is this needed.
      // A good point to start: test/trace/reg0048.trace.
      assert (stats.solves);
    }
    internal->propagated = 0;
    if (internal->propagate ()) {
      internal->backtrack ();
      return false;
    }
    STOP (drup_repropagate);
  }
  STOP (drup_propagate);
  return true;
}


void Drupper::conflict_analysis_core () {
  START (drup_analyze);
  Clause * conflict = internal->conflict;
  assert(conflict);
  mark_core (conflict);

  auto got_value_by_propagation = [this](int lit) {
    assert (internal->val (lit) != 0);
#ifndef NDEBUG
    int trail = internal->var (lit).trail;
    assert (trail >= 0 && trail < int (internal->trail.size()));
    assert (internal->trail[trail] == -lit);
#endif
    return internal->var (lit).trail > internal->control.back().trail;
  };

  ///TODO: Use internal->mark|ed () instead.
  unordered_set<int> seen;

  for (int lit : *conflict)
  {
    Var & v = internal->var(lit);
    assert (v.level > 0 || v.reason);
    if (got_value_by_propagation (lit))
      seen.insert (abs(lit));
    else if (!v.level)
      mark_core (v.reason);
  }

  for (int i = internal->trail.size()-1; i > internal->control.back().trail; i--)
  {
    int lit = internal->trail[i];
    Var & v = internal->var(lit);

    if (!seen.count (abs(lit)))
      continue;
    seen.erase (abs(lit));

    Clause * c = v.reason;
    mark_core (c);

#ifndef NDEBUG
    assert (internal->var(c->literals[0]).reason == c);
    assert (internal->val(c->literals[0]) > 0);
    assert (c->literals[0] == lit);
#endif

    for (int j = 1; j < c->size; j++)
    {
      int lit = c->literals[j];
      Var & v = internal->var(lit);
      assert(internal->val(lit) < 0);
      if (got_value_by_propagation (lit))
        seen.insert (abs(lit));
      else if (!v.level) {
        mark_core (v.reason);
      }
    }
  }

  assert (seen.empty ());
  STOP (drup_analyze);
}

/*------------------------------------------------------------------------*/

static void collect (Internal * internal) {
  if (!internal->protected_reasons)
    internal->protect_reasons ();
  internal->delete_garbage_clauses ();
  internal->unprotect_reasons ();
}

/*------------------------------------------------------------------------*/

void Drupper::mark_core_trail_antecedents () {
  START (drup_mark_antecedents);
  for (int i = internal->trail.size() - 1; i >= 0; i--) {
    int lit = internal->trail[i];
    Clause * reason = internal->var (lit).reason;
    assert (reason);
    if (reason->core) {
      assert (reason->literals[0] == lit);
      for (int lit : *reason)
        mark_core (internal->var (lit).reason);
      internal->propagated = i;
      ///TODO: set internal->propagated2
    }
  }
  STOP (drup_mark_antecedents);
}

void Drupper::unmark_core_clauses () {
  for (Clause * c : internal->clauses)
    if (c->core)
      c->core = false, stats.core--;
  for (Clause * c : clauses)
    if (c->core)
      c->core = false, stats.core--;
  for (Clause * c : unit_clauses)
    if (c->core)
      c->core = false, stats.core--;
  assert (stats.core == 0);
}

void Drupper::restore_trail () {
  lock_scope isolate (isolated);
  // Restoring the trail is done with respect to the order of literals.
  // Each unit is allocated in the same order it's pushed the trail.
  for (Clause * c : unit_clauses) {
    const int lit = c->literals[0];
    if (internal->val (lit)) continue;
    internal->search_assign (lit, c);
    internal->propagate ();
  }
}

void Drupper::clear_failing (const unsigned proof_sz) {
  if (failed_constraint) {
    internal->unwatch_clause (failed_constraint);
    delete [] (char *) failed_constraint;
    failed_constraint = 0;
  }
  if (proof.size () == proof_sz) return;
  int pop = proof.size () - proof_sz;
  while (pop--) {
    if (proof.back ()->deleted)
      stats.deleted--;
    else
      stats.derived--;
    proof.pop_back ();
  };
}

void Drupper::reallocate () {
  assert (isolated);
  for (DrupperClause * dc : proof) {
    Clause * c = dc->clause ();
    if (!dc->deleted) {
      assert (c);
      assert (!dc->revive_at);
      assert (c->garbage);
      c->garbage = false;
      if (c->size > 1)
        internal->watch_clause (c);
    }
  }

  for (int i = proof.size () - 1; i >= 0; i--) {
    DrupperClause * dc = proof[i];
    if (dc->deleted) {
      Clause * c = dc->clause ();
      assert (c && !c->garbage);
      c->garbage = true;
      assert (!is_on_trail (c) || c->size == 1);
    }
  }

  if (!internal->protected_reasons)
    internal->protect_reasons ();
  internal->flush_all_occs_and_watches ();
  internal->unprotect_reasons ();

#ifndef NDEBUG
  int revived_units = 0;
#endif
  for (int i = proof.size () - 1; i >= 0; i--) {
    DrupperClause * dc = proof[i];
    if (dc->deleted) {
      Clause * c = dc->clause ();
      assert (c && c->garbage);
      reset_counterpart (dc);
      if (dc->revive_at)
        reset_counterpart (proof[dc->revive_at - 1]); // No need to fill the literals here?
      if (c->size > 1)
        delete [] (char*) c;
#ifndef NDEBUG
      else revived_units++;
#endif
    }
  }
#ifndef NDEBUG
  assert (revived_units < 2);
#endif
  clauses.clear ();
}

void Drupper::reconstruct (const unsigned proof_sz) {
  lock_scope isolate (isolated);
  START (drup_reconstruct);
  save_core_phase_stats ();
  unmark_core_clauses ();
  reallocate ();
  clear_failing (proof_sz);
  collect (internal);
  STOP (drup_reconstruct);
}

/*------------------------------------------------------------------------*/

void Drupper::check_environment () const {
#ifndef NDEBUG
  assert (proof.size() == unsigned(stats.derived + stats.deleted));
  for (unsigned i = 0; i < proof.size(); i++) {
    DrupperClause * dc = proof[i];
    assert (dc);
    if (dc->deleted) {
      assert (dc->variant_type () == LITERALS);
      assert (dc->variant_type () == LITERALS && dc->lits ().size ());
      if (dc->revive_at) {
        assert (dc->revive_at <= proof.size ());
        assert (dc->revive_at > 0);
        assert (!proof[dc->revive_at-1]->revive_at);
        assert (!proof[dc->revive_at-1]->deleted);
        assert (proof[dc->revive_at-1]->variant_type () == LITERALS);
        assert (proof[dc->revive_at-1]->lits ().size ());
      }
    } else {
      assert (dc->variant_type () == CLAUSE || dc->lits ().size ());
    }
    if (dc->variant_type () == CLAUSE) {
      Clause * c = dc->clause ();
      if (!dc->deleted && c && c->garbage) {
        ///NOTE: See the discussion in 'propagate' on avoiding to eagerly trace binary
        // clauses as deleted (produce 'd ...' lines) as soon they are marked
        // garbage.
        assert (c->size == 2);
        assert (0 && "remove this if you are actually delaying the trace of garbage binaries");
      }
    }
  }
#endif
}

void Drupper::dump_clauses (bool active) const {
  printf ("DUMP CLAUSES START\n");
  int j = unit_clauses.size() - 1;
  for (int i = internal->clauses.size () - 1; i >= 0; i--) {
    Clause * c = internal->clauses[i];
    if (active && c->garbage && c->size != 2)
      continue;
    printf ("(%d) %s: ", i + j + 1, c->garbage ? "garbage" : "       ");
    printf ("(%lu): ", c);
    for (int j = 0; j < c->size; j++) printf ("%d ", c->literals[j]);
    printf ("\n");
  }
  for (; j >= 0; j--) {
    Clause * c = unit_clauses[j];
    if (active && c->garbage && c->size != 2)
      continue;
    printf ("(%d) %s: ", j, c->garbage ? "garbage" : "       ");
    printf ("c: ");
    for (int j = 0; j < c->size; j++) printf ("%d ", c->literals[j]);
    printf ("\n");
  }
  printf ("DUMP CLAUSES END\n");
}

void Drupper::dump_clause (const Clause * c) const {
  if (!c) printf ("0 \n");
  else {
    for (int lit : *c)
      printf ("%d ", lit);
    printf ("\n");
  }
}

void Drupper::dump_clause (const DrupperClause * dc) const {
  assert (dc);
  const auto & lits = dc->lits ();
  for (int i : lits)
    printf ("%d ", i);
  printf ("\n");
}

void Drupper::dump_clause (const vector <int> & c) const {
  for (int i : c)
    printf ("%d ", i);
  printf ("\n");
}

void Drupper::dump_proof () const {
  printf ("DUMP PROOF START\n");
  for (int i = proof.size () - 1; i >= 0; i--) {
    auto & dc = proof[i];
    printf ("(%d) %s: ", i, dc->deleted ? "deleted" : "       ");
    if (dc->variant_type () == LITERALS) {
      auto & lits = dc->lits ();
      for (int l : lits)
        printf ("%d ", l);
    } else {
      Clause * c = proof[i]->clause ();
      printf ("c: ");
      if (!c) printf ("0 ");
      else {
        for (int lit : *c) printf ("%d ", lit);
        printf ("%s", c->garbage ? "(garbage)" : "");
      }
    }
    printf ("\n");
  }
  printf ("DUMP PROOF END\n");
}

void Drupper::dump_trail () const {
  printf ("DUMP TRAIL START\n");
  auto & trail = internal->trail;
  for (int i = trail.size () - 1; i >= 0; i--)
    printf ("(%d) %d <-- ", i, trail[i]), dump_clause (internal->var (trail[i]).reason);
  printf ("DUMP TRAIL END\n");
}

bool Drupper::core_is_unsat () const {
  CaDiCaL::Solver s;
  s.set ("drup", 0);
  for (Clause * c : internal->clauses)
    if (c->core) {
      for (int * i = c->begin (); i != c->end (); i++)
        s.add (*i);
      s.add (0);
    }
  for (Clause * c : clauses)
    if (c->core) {
      for (int * i = c->begin (); i != c->end (); i++)
        s.add (*i);
      s.add (0);
    }
  for (Clause * c : unit_clauses)
    if (c->core) {
      s.add (c->literals[0]);
      s.add (0);
    }
  for (int l : internal->assumptions)
    if (internal->failed (l)) {
      s.add (l);
      s.add (0);
    }
  if (internal->unsat_constraint && internal->constraint.size () == 1) {
    for (int i : internal->constraint)
      s.add (i);
    s.add (0);
  } // Otherwise should be part if internal->clauses
  return s.solve () == 20;
}

void Drupper::dump_core () const {
  if (!internal->opts.drupdumpcore || !file)
    return;
  file->put ("DUMP CORE START\n");
  for (Clause * c : internal->clauses)
    if (c->core) {
      for (int * i = c->begin (); i != c->end (); i++)
        file->put (*i), file->put (' ');
      file->put ("0\n");
    }
  for (Clause * c : clauses)
    if (c->core) {
      for (int * i = c->begin (); i != c->end (); i++)
        file->put (*i), file->put (' ');
      file->put ("0\n");
    }
  for (Clause * c : unit_clauses)
    if (c->core) {
      file->put (c->literals[0]);
      file->put (" 0\n");
    }
  for (int l : internal->assumptions)
    if (internal->failed (l)) {
      file->put (l);
      file->put (" 0\n");
    }
  if (internal->unsat_constraint && internal->constraint.size () == 1) {
    for (int i : internal->constraint)
      file->put (i), file->put (' ');
    file->put ("0\n");
  } // Otherwise should be part if internal->clauses
  file->put ("DUMP CORE START\n");
}

vector<int> Drupper::extract_core_literals () const {
  vector<int> core_lits;
  for (Clause * c : internal->clauses)
    if (c->core)
      for (int l : *c)
        if (!internal->flags (l).mark_core (true))
          core_lits.push_back (l);
  for (Clause * c : clauses)
    if (c->core)
      for (int l : *c)
        if (!internal->flags (l).mark_core (true))
          core_lits.push_back (l);
  for (Clause * c : unit_clauses)
    if (c->core)
      for (int l : *c)
        if (!internal->flags (l).mark_core (true))
          core_lits.push_back (l);
  for (int l : internal->assumptions)
    if (!internal->flags (l).mark_core (true))
      core_lits.push_back (l);
  if (internal->unsat_constraint && internal->constraint.size () == 1) {
    int l = internal->constraint[0];
    if (!internal->flags (l).mark_core (true))
      core_lits.push_back (l);
  }
  // Otherwise should be part if internal->clauses
  return core_lits;
}

/*------------------------------------------------------------------------*/

void Drupper::add_derived_clause (Clause * c) {
  if (isolated) return;
  assert (!validating);
  START (drup_inprocess);
  LOG (c, "DRUPPER derived clause notification");
  append_lemma (new DrupperClause (), c);
  STOP (drup_inprocess);
}

void Drupper::add_derived_unit_clause (const int lit, bool original) {
  if (isolated) return;
  assert (!validating);
  START (drup_inprocess);
  LOG ({lit}, "DRUPPER derived clause notification");
  assert (lit);
  assert (!original || !internal->var(lit).reason);
  Clause * c = 0;
  if (!internal->var(lit).reason)
    internal->var(lit).reason = c = new_unit_clause (lit, original);
  if (!original) {
    c = !c ? new_unit_clause (lit, original) : c;
    append_lemma (new DrupperClause (), c);
  }
  assert (internal->var(lit).reason->literals[0] == lit);
  STOP (drup_inprocess);
}

void Drupper::add_derived_empty_clause () {
  if (isolated) return;
  assert (!validating);
  START (drup_inprocess);
  LOG ("DRUPPER derived empty clause notification");
  STOP (drup_inprocess);
}

void Drupper::add_failing_assumption (const vector<int> & c) {
  if (isolated) return;
  assert (!validating);
  if (c.size () > 1) {
    // See ../interesting_tests/assump_and_constraint
    if (!trivially_satisfied (c))
      append_failed (c);
  } else {
    Clause * r = internal->var (c[0]).reason;
    if (r) mark_core (r);
  }
}

void Drupper::add_updated_clause (Clause * c) {
  if (isolated) return;
  assert (!validating && c);
  START (drup_inprocess);
  LOG (c, "DRUPPER updated");
  unsigned revive_at = 0;
  if (c->drup_idx) {
    revive_at = c->drup_idx;
    assert (proof[revive_at - 1]->clause () == c);
    reset_counterpart (proof[revive_at - 1]);
  }
  append_lemma (new DrupperClause (), c);
  append_lemma (new DrupperClause (c, true), 0);
  proof[proof.size ()-1]->revive_at = revive_at;
  STOP (drup_inprocess);
}

/*------------------------------------------------------------------------*/

// Must be called at a point in which no literals are marked!
static vector<int> remove_duplicates (Internal * internal, const vector <int> & c) {
  vector<int> unique;
  for (int lit : c) {
    if (internal->marked (lit))
      continue;
    internal->mark (lit);
    unique.push_back (lit);
  }
  for (int lit : unique)
    internal->unmark (lit);
  return unique;
}

static void swap_falsified_literals_right (Internal * internal, vector <int> & c) {
  int sz = c.size ();
  for (int i = 0; i < sz; i++) {
    if (internal->val (c[i]) < 0) {
      int bl = c[--sz];
      c[sz] = c[i];
      c[i] = bl;
    }
  }
}

/*------------------------------------------------------------------------*/

void Drupper::delete_clause (const vector<int> & c, bool original) {
  if (isolated) return;
  assert (!validating);
  START (drup_inprocess);
  LOG (c, "DRUPPER clause deletion notification");
  // remove duplicates. if there is only one unique literal,
  // skip it unless it's a falsified original then we cache it.
  vector<int> modified = remove_duplicates (internal, c);
  bool falsified_original = modified.size () == 1 && internal->val (c[0]) < 0;
  if (modified.size () == c.size () || modified.size () > 1 || falsified_original) {
    if (original) {
      ///NOTE: This is an original clause that has been reduced to an irredundant
      // dervied clause after removing all its falsified literals. This clause was
      // not allocated in memory. However, it needs to be revived for correct core
      // extraction and complete validation.
      // Moving the falsified literals to the end of the clause is crucial as we
      // need to watch the first two unassigned literals of this clause once it is
      // revived.
      swap_falsified_literals_right (internal, modified);
    }
    append_lemma (new DrupperClause (modified, true), 0);
  }
  STOP (drup_inprocess);
}

void Drupper::delete_clause (Clause * c) {
  if (isolated) return;
  assert (!validating);
  START (drup_inprocess);
  LOG (c, "DRUPPER clause deletion notification");
  append_lemma (new DrupperClause (c, true), c);
  STOP (drup_inprocess);
}

/*------------------------------------------------------------------------*/

void Drupper::update_moved_counterparts () {
  if (isolated) return;
  assert (!validating);
  START (drup_inprocess);
  for (unsigned i = 0; i < proof.size(); i++) {
    auto & dc = proof[i];

    if (dc->deleted || dc->variant_type () == LITERALS)
      continue;

    Clause * c = dc->clause ();
    if (!c->moved)
      continue;

#ifndef NDEBUG
    assert (c->copy && c != c->copy);
    assert (c->drup_idx);
    assert (c->copy->drup_idx);
#endif

    c->copy->drup_idx = c->drup_idx;
    reset_counterpart (dc);
    set_counterpart (dc, c->copy);
  }
  STOP (drup_inprocess);
}

/*------------------------------------------------------------------------*/

optional<vector<int>> Drupper::trim (bool overconstrained) {
  START (drup_trim);
  LOG ("DRUPPER trim");

  stats.solves++;

  save_scope<bool> recover_unsat (internal->unsat);
  assert (!validating && !isolated && !setup_internal_options ());
  check_environment ();

  // Mark the conflict and its reasons as core.
  const unsigned proof_sz = proof.size ();
  mark_conflict (overconstrained);

  clean_conflict ();
  // 'trail_sz' is used for lazy shrinking of the trail.
  unsigned trail_sz = internal->trail.size();
  lock_scope trim_scope (validating);

  collect (internal);

  // Main trimming loop
  for (int i = proof.size() - 1 - int (overconstrained); i >= 0; i--) {
    auto & dc = proof[i];
    bool deleted = dc->deleted;

    assert (!deleted || dc->variant_type () == LITERALS);

    if (deleted) {
      revive_clause (i);
      continue;
    }

    if (proof_sz == i)
      mark_failing (proof_sz);

    Clause * c = proof[i]->clause ();

    if (is_on_trail (c)) {
      if (settings.core_units)
        mark_core (c);
      undo_trail_core (c, trail_sz);
      internal->report ('m');
    }

    stagnate_clause (i);

    if (c->core) {
      shrink_internal_trail (trail_sz);
      assume_negation (c);
      bool validated = propagate_conflict ();
      assert (validated);
      conflict_analysis_core ();
      clean_conflict ();
    }
  }

  shrink_internal_trail (trail_sz);
  mark_core_trail_antecedents ();

  internal->report ('M');

  {
    // This is a good point to dump core as garbage core clauses will be removed later.
    dump_core ();
    #ifndef NDEBUG
      // Ensure the set of all core clauses is unsatisfiable
      if (settings.check_core)
        assert (core_is_unsat ());
    #endif
  }

  optional<vector<int>> opt_core_lits = {};

  if (settings.extract_core_literals)
    opt_core_lits = extract_core_literals ();

  ///NOTE: In typical scenarios, once the formula undergoes trimming in primary applications, the
  // solver ceases further solving efforts. Nevertheless, in cases where the user desires to persist
  // with solving post-trimming, it becomes necessary to restore the solver's state.
  // This process involves:
  // 1) Removing marks from core clauses to permit formula trimming anew (useful for testing purposes).
  // 2) Connecting detached clauses again and deallocating resources that have been allocated during trim().
  if (settings.reconstruct)
    reconstruct (proof_sz);

  restore_trail ();

  STOP (drup_trim);
  return opt_core_lits;
}

void Drupper::sort_watches (const int lit) {
  auto & ws = internal->watches (lit);
  int l = 0, h = ws.size () - 1;
  while (l < h) {
    auto w = ws[h];
    if (!w.clause->core) {
      h--;
      continue;
    }
    auto tw = ws[l];
    ws[l++] = ws[h];
    ws[h] = tw;
  }
}

}
