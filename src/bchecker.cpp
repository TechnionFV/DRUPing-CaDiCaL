#include "internal.hpp"
#include "unordered_set"

namespace CaDiCaL {

static void pc (const vector<int> c) {
  for (unsigned i = 0; i < c.size(); i++)
    printf ("%d ", c[i]);
  printf ("\n");
}

static void pc (const BCheckerClause * c) {
  if (!c) {
    printf("0\n");
    return;
  }
  for (unsigned i = 0; i < c->size; i++)
    printf ("%d ", c->literals[i]);
  printf ("\n");
}

static void pc (const Clause * c) {
  if (!c) {
    printf("0\n");
    return;
  }
  for (int i = 0; i < c->size; i++)
    printf ("%d ", c->literals[i]);
  printf ("\n");
}

/*------------------------------------------------------------------------*/

BChecker::BChecker (Internal * i, bool core_units)
:
  internal (i), inconsistent (false),
  num_clauses (0), size_clauses (0), clauses (0),
  core_units (core_units), validating (0)
{
  LOG ("BCHECKER new");

  // Initialize random number table for hash function.
  //
  Random random (42);
  for (unsigned n = 0; n < num_nonces; n++) {
    uint64_t nonce = random.next ();
    if (!(nonce & 1)) nonce++;
    assert (nonce), assert (nonce & 1);
    nonces[n] = nonce;
  }

  // Initialize statistics.
  //
  memset (&stats, 0, sizeof (stats));
}

BChecker::~BChecker () {
  LOG ("BCHECKER delete");
  for (size_t i = 0; i < size_clauses; i++)
    for (BCheckerClause * c = clauses[i], * next; c; c = next)
      next = c->next, delete_clause (c);
  delete [] clauses;
}

/*------------------------------------------------------------------------*/

uint64_t BChecker::reduce_hash (uint64_t hash, uint64_t size) {
  assert (size > 0);
  unsigned shift = 32;
  uint64_t res = hash;
  while ((((uint64_t)1) << shift) > size) {
    res ^= res >> shift;
    shift >>= 1;
  }
  res &= size - 1;
  assert (res < size);
  return res;
}

uint64_t BChecker::compute_hash (const vector<int> & simplified) {
  ///TODO: Hash isn't order insinsetive. Since internal Clause objects
  //  are prone to reordering we must have an order insensitive hash computation.
  //  In the meantime, sort before computing the hash value.
  auto sorted (simplified); sort(sorted.begin (), sorted.end ());
  unsigned i = 0, j = 0;
  uint64_t hash = 0;
  for (i = 0; i < sorted.size (); i++) {
    int lit = sorted[i];
    hash += nonces[j++] * (uint64_t) lit;
    if (j == num_nonces) j = 0;
  }
  return hash;
}

void BChecker::enlarge_clauses () {
  assert (num_clauses == size_clauses);
  const uint64_t new_size_clauses = size_clauses ? 2*size_clauses : 1;
  LOG ("BCHECKER enlarging clauses of checker from %" PRIu64 " to %" PRIu64,
    (uint64_t) size_clauses, (uint64_t) new_size_clauses);
  BCheckerClause ** new_clauses;
  new_clauses = new BCheckerClause * [ new_size_clauses ];
  clear_n (new_clauses, new_size_clauses);
  for (uint64_t i = 0; i < size_clauses; i++) {
    for (BCheckerClause * c = clauses[i], * next; c; c = next) {
      next = c->next;
      const uint64_t h = reduce_hash (c->hash, new_size_clauses);
      c->next = new_clauses[h];
      new_clauses[h] = c;
    }
  }
  delete [] clauses;
  clauses = new_clauses;
  size_clauses = new_size_clauses;
}

BCheckerClause ** BChecker::find (Clause * c) {
  stats.searches++;
  BCheckerClause ** res, * bc;
  const auto size = c->size;
  vector<int> lits;
  unordered_set<int> marks;
  for (int i = 0; i < size; i++) {
    lits.push_back (c->literals[i]);
    marks.insert (lits[i]);
  }
  assert (marks.size () == size);
  const uint64_t hash = compute_hash (lits);
  const uint64_t h = reduce_hash (hash, size_clauses);
  for (res = clauses + h; (bc = *res); res = &bc->next) {
    if (bc->hash == hash && bc->size == size) {
      bool found = true;
      const int * literals = c->literals;
      for (unsigned i = 0; found && i != size; i++)
        found = marks.count(literals[i]);
      if (found) break;
    }
    stats.collisions++;
  }
  return res;
}

BCheckerClause ** BChecker::find (const vector<int> & simplified) {
  stats.searches++;
  BCheckerClause ** res, * c;
  const uint64_t hash = compute_hash (simplified);
  const unsigned size = simplified.size ();
  const uint64_t h = reduce_hash (hash, size_clauses);
  unordered_set<int> marks;
  for (unsigned i = 0; i < size; ++i)
    marks.insert (simplified[i]);
  // The only preprocessing we should do is to remove duplicates.
  assert (marks.size () == size);
  for (res = clauses + h; (c = *res); res = &c->next) {
    if (c->hash == hash && c->size == size) {
      bool found = true;
      const int * literals = c->literals;
      for (unsigned i = 0; found && i != size; i++)
        found = marks.count(literals[i]);
      if (found) break;
    }
    stats.collisions++;
  }
  return res;
}

BCheckerClause * BChecker::new_clause (const vector<int> & simplified, const uint64_t hash) {
  const size_t size = simplified.size ();
  assert (0 < size && size <= UINT_MAX);
  const size_t surplus_bytes = size - 1;
  const size_t bytes = sizeof (BCheckerClause) + (surplus_bytes-1) * sizeof (int);
  BCheckerClause * res = (BCheckerClause *) new char [bytes];
  res->next = 0;
  res->counterpart = 0;
  res->hash = hash;
  res->size = size;
  res->garbage = false;
  int * literals = res->literals;
  int * p = literals;
  for (const auto & lit : simplified)
    *p++ = lit;

  num_clauses++;

  return res;
}

void BChecker::delete_clause (BCheckerClause * c) {
  assert (c->size > 0);
  assert (num_clauses);
  num_clauses--;
  delete [] (char*) c;
}

BCheckerClause * BChecker::insert (Clause * c) {
  stats.insertions++;
  if (num_clauses == size_clauses) enlarge_clauses ();
  vector<int> lits;
  for (int i = 0; i < c->size; i++)
    lits.push_back (c->literals[i]);
  uint64_t hash = compute_hash (lits);
  const uint64_t h = reduce_hash (hash, size_clauses);
  BCheckerClause * bc = new_clause (lits, hash);
  assert (counterparts[bc].empty());
  bc->next = clauses[h];
  clauses[h] = bc;
  return bc;
}

BCheckerClause * BChecker::insert (const vector<int> & simplified) {
  stats.insertions++;
  if (num_clauses == size_clauses) enlarge_clauses ();
  uint64_t hash = compute_hash (simplified);
  const uint64_t h = reduce_hash (hash, size_clauses);
  BCheckerClause * c = new_clause (simplified, hash);
  c->next = clauses[h];
  clauses[h] = c;
  return c;
}

///TODO: Avoid unnecessary allocations and reuse valid garbage Clause references when possible.
void BChecker::revive_internal_clause (BCheckerClause * bc) {
  assert (bc->garbage && !bc->counterpart);
  Clause * c = nullptr;
  if (bc->size == 1) {
    int lit = bc->literals[0];
    c = bc->counterpart = internal->new_unit_clause (lit, false);
    if (!internal->val (lit))
      internal->search_assign (lit, c);
  } else {
    assert (internal->clause.empty());
    for (unsigned i = 0; i < bc->size; i++)
      internal->clause.push_back (bc->literals[i]);
    // Only redundant clauses can be deleted.
    c = bc->counterpart = internal->new_clause (true);
    internal->clause.clear();
    internal->watch_clause (c);
  }

  assert (c && !c->reason);
  assert (bc->counterpart == c);
  bc->garbage = false;
}

void BChecker::stagnate_internal_clause (BCheckerClause * bc) {
  assert (bc && !bc->garbage && bc->counterpart);
  Clause * c = bc->counterpart;
  if (c->size > 1)
    internal->unwatch_clause (c);
  internal->mark_garbage (c);
  bc->garbage = true;
  ///TODO: Decide either to invalidate counterpart reference or
  // to cancel the garbage collection during validation. Might be
  // better to reuse the same reference if stil valid instead of
  // allocating a new one.
  bc->counterpart = 0;
}

bool BChecker::shrink_internal_trail (const int trail_sz) {
  if (trail_sz >= internal->trail.size())
    return false;
  internal->trail.resize(trail_sz);
  internal->propagated = trail_sz;

  {
    // just to understand what is happening
    //
    assert (!internal->level);
    assert(internal->control.size () == 1);
  }

  return true;
}

// The internal solver does not support reactivation of
// fixed literals. However, this is needed to be able to
// propagate these literals again.
void BChecker::reactivate_fixed (int l) {
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

void BChecker::undo_trail_literal (int lit) {
  assert (internal->val (lit) > 0);
  if (!internal->active (lit))
    reactivate_fixed (lit);
  internal->unassign (lit);
  assert (!internal->val (lit));
  assert (internal->active (lit));
  assert (internal->var(lit).reason);
  internal->var(lit).reason->reason = false;
  internal->var(lit).reason = 0;
}

void BChecker::undo_trail_core (Clause * c, unsigned & trail_sz) {
  LOG ("BCHECKER undoing trail core");
  assert (c && trail_sz > 0 && c->size > 0);
  assert (trail_sz <= internal->trail.size());
  int clit = c->literals[0];
  assert (internal->var(clit).reason == c);

  while (internal->trail[trail_sz - 1] != clit)
  {
    assert(trail_sz > 1);

    int l = internal->trail[--trail_sz];

    Clause * r = internal->var(l).reason;
    assert (r);

    undo_trail_literal (l); // sets r->reason to false

    if (core_units) mark_core (r);

    if (r->core)
      for (int j = 1; j < r->size; j++)
      {
        Clause * reason = internal->var(r->literals[j]).reason;
        assert (reason);
        mark_core (reason);
      }
  }
  assert(clit == internal->trail[--trail_sz]);
  undo_trail_literal (clit);
}

bool BChecker::is_on_trail (BCheckerClause * bc) {
  assert (internal->protected_reasons);
  assert (bc);
  int lit = bc->literals[0];
  return internal->val(lit) > 0 && internal->var(lit).reason == bc->counterpart;
}

void BChecker::mark_core (Clause * c) {
  assert (c);
  c->core = true;
}

void BChecker::conflict_analysis_core () {

  Clause * conflict = internal->conflict;
  assert(conflict);
  mark_core (conflict);

  ///TODO: Check this is correct even when chronological backtraking is on (internal->opts.chrono).
  // Need to check with https://cca.informatik.uni-freiburg.de/papers/MoehleBiere-SAT19.pdf
  auto got_value_by_propagation = [this](Var & v) {
    return v.trail > internal->control.back().trail && v.trail < internal->propagated;
  };

  for (int i = 0; i < conflict->size; i++)
  {
    int lit = conflict->literals[i];
    Var & v = internal->var(lit);
    assert (v.level > 0 || v.reason);
    if (got_value_by_propagation (v) && !internal->marked (abs (lit)))
      internal->mark(abs(lit));
    else if (!v.level)
      mark_core (v.reason);
  }

  for (int i = internal->propagated-1; i > internal->control.back().trail; i--)
  {
    int lit = internal->trail[i];
    Var & x = internal->var(lit);
    if (!internal->marked(abs(lit)))
      continue;

    internal->unmark(abs(lit));

    Clause * c = x.reason;
    assert (c);

    mark_core (c);

    assert (internal->var(c->literals[0]).reason == c);
    assert (internal->val(c->literals[0]) > 0);

    for (int j = 1; j < c->size; j++)
    {
      int lit = c->literals[j];
      Var & y = internal->var(lit);
      assert(internal->val(lit) < 0);
      if (got_value_by_propagation (y) && !internal->marked (abs(lit)))
        internal->mark (abs(lit));
      else if (!y.level)
        assert (y.reason), mark_core (y.reason);
    }
  }
}

static void dump_trail (Internal * internal, int verb = 0, int d = 0) {
  printf ("trail is partitioned into %d partitions: ", internal->control.size());
  for (int i = 0; i < internal->control.size(); i++)
    if (i == internal->control.size()-1)
      printf ("[%d-%d]\n", internal->control[i].trail, internal->trail.size()-1);
    else
      printf ("[%d-%d], ", internal->control[i].trail, internal->control[i+1].trail);
  if (verb > 0) {
    printf("last propagation has reasoned the following literals: ");
    for (int i = internal->control.back().trail + d; i < internal->propagated; i++) {
      printf ("%d ", internal->trail[i]);
      if (verb > 1) {
        Clause * r = internal->var (internal->trail[i]).reason;
        assert (r);
        printf ("from (");
        for (int m = 0; m < r->size; m++)
          printf (" %d", r->literals[m]);
        printf (") ");
      }
    }
    printf ("\n");
    printf("last propagation has reasoned the following conflict: "); pc (internal->conflict);
  }
}

bool BChecker::validate_lemma (Clause * lemma) {
  assert (validating);
  assert(!internal->level);
  assert(lemma && lemma->core);
  assert (internal->propagated == internal->trail.size ());

  vector <int> decisions;
  for (int i = 0; i < lemma->size; i++) {
    int lit = lemma->literals[i];
    if (!internal->val(lit))
      decisions.push_back (-lit);
    else {
      assert (internal->var(lit).reason);
      assert (internal->var(lit).level == 0);
      mark_core (internal->var(lit).reason);
    }
  }

  assert (decisions.size());
  internal->search_assume_multiple_decisions (decisions);
  assert (internal->level  == decisions.size());

  assert(!internal->conflict);
  if (internal->propagate ())
  {
    ///TODO: This might happen according to the Minisat patch.
    // -- If propagate fails, it may be due to incrementality and missing
    // -- units. Update qhead and re-propagate the entire trail
    internal->propagated = 0;
    if (internal->propagate ()) {
      internal->backtrack ();
       return false;
    }
  }

  // printf ("after propagation: ");
  // dump_trail (internal, 2, decisions.size());

  conflict_analysis_core ();

  internal->backtrack ();
  internal->conflict = 0;
  return true;
}

void BChecker::mark_core_trail_antecedents () {
  ///TODO: Needs to be implemented
}

void BChecker::check_counterparts () {
  for (uint64_t i = 0; i < size_clauses; i++)
    for (BCheckerClause * bc = clauses[i]; bc; bc = bc->next) {
      assert (bc);
      vector<Clause *>& cps = counterparts[bc];
      if (bc->garbage) assert (cps.empty());
      else if (bc->size == 2 && !cps.empty() && cps[0]->garbage) {
        // The proof isn't notified with deleted binary
        // clauses until they are actually deallocated.
        stats.deleted++;
        bc->garbage = true;
        cps.clear();
      } else {
        assert (cps.size());
        for (Clause * c : cps) {
          assert (c && !c->moved && !c->garbage);
          unordered_set <int> marks1, marks2;
          assert (unsigned(c->size) == bc->size);
          for (int l = 0; l < bc->size; l++) {
            marks1.insert (bc->literals[l]);
            marks2.insert (c->literals[l]);
          }
          assert (marks1 == marks2);
        } 
      }
    }
}

bool BChecker::validate () {
  assert (inconsistent);
  assert (proof.size ());
  assert (internal->unsat);

  START (bchecking);
  LOG ("BCHECKER starting validation");

  validating = true;

  // printf ("befote validation: "), dump_trail (internal, 3);

  // printf ("proof contains:\n");
  // for (int i = proof.size()-1; i >= 0; i--) pc (proof[i]);

  ///NOTE: Assert that conflicting assumptions and failing constraint
  // are being cached as learnt clauses if any (revisit src/assume.cpp).

  // 'protect_reasons' should protect fixed literal reasons as well.
  //
  ///TODO: Check which has more overhead:
  // 1- either protect all reasons once and check ->reason flag
  // 2- or use the Minisat way (Solver::locked ()).
  if (!internal->protected_reasons)
    internal->protect_reasons();
  internal->flush_all_occs_and_watches ();

  check_counterparts ();
  return 1;
  Clause * last_conflict = internal->conflict;
  assert (last_conflict); // for workaround.
  mark_core (last_conflict);

  ///TODO: final conflict under assumptions
  // contains only one literal, mark all reasons.
  // Mark all conflict reasons as core
  for (int i = 0; i < last_conflict->size; i++) {
    assert (internal->val(last_conflict->literals[i]) < 0);
    Var & v = internal->var(last_conflict->literals[i]);
    Clause * reason = v.reason;
    if (reason) mark_core (reason);
  }

  internal->unsat = false;
  internal->backtrack();
  internal->conflict = 0;

  unsigned trail_sz = internal->trail.size();

  for (int i = proof.size() - 1; i >= 0; i--) {
    BCheckerClause * bc = proof[i];
    assert(bc && bc->size);

    if (bc->garbage) {
      revive_internal_clause (bc);
      continue;
    }

    Clause * c = bc->counterpart;
    assert (c && !bc->garbage && !c->garbage);

    if (is_on_trail (bc)) {
      if (core_units) mark_core (c);
      // put_trail_literal_in_place (c);
      assert (internal->val(c->literals[0]) > 0);
      undo_trail_core (c, trail_sz);
      assert (!internal->val (c->literals[0]));
    }

    stagnate_internal_clause (bc);

    ///TODO: According to the paper, this should be conditioned with 'if not initial clause'.
    //       However, this isn't being done in Minisat patch.
    if (c->core) {
      shrink_internal_trail (trail_sz);
      if (!validate_lemma (c)) goto exit;
    }
  }

  shrink_internal_trail (trail_sz);

  /// TODO: find core clauses in the rest of the trail.
  mark_core_trail_antecedents ();

  /// TODO: Put units back on the trail.

  internal->flush_all_occs_and_watches ();

  ///TODO: Clean up internal clauses that were created for validation purposes.

  printf ("Core lemmas are: \n");
  for (unsigned i = 0; i < internal->clauses.size (); i++) {
    if (internal->clauses[i]->garbage) continue;
    if (internal->clauses[i]->core)
      pc (internal->clauses[i]);
  }

  validating = false;

exit:
  STOP (bchecking);
  ///TODO: Find a less ugly way of doing this :)
  if (validating)
    return validating = false;
  else return true;
}

/*------------------------------------------------------------------------*/

void BChecker::add_derived_clause (Clause * c) {
  if (inconsistent) return;
  START (bchecking);
  LOG (c, "BCHECKER derived clause notification");
  stats.derived++;
  assert (c && c->size > 1);
  BCheckerClause * bc = num_clauses > 0 ? *find(c) : 0;
  if (bc) {
    auto it = std::find(counterparts[bc].begin(), counterparts[bc].end(), c);
    if (it == counterparts[bc].end()) counterparts[bc].push_back (c);
  } else {
    bc = insert (c);
    counterparts[bc].push_back (c);
  }
  assert (bc);
  proof.push_back (bc);
  STOP (bchecking);
}

void BChecker::add_derived_unit_clause (const int lit) {
  if (inconsistent) return;
  START (bchecking);
  LOG (c, "BCHECKER derived clause notification");
  stats.derived++;
  assert (lit);
  BCheckerClause * bc = num_clauses > 0 ? *find({lit}) : 0;
  Clause * r = internal->var(lit).reason;
  assert (!bc || r);
  if (!bc) bc = insert ({lit});
  assert (bc);
  vector<Clause *> & cps = counterparts[bc];
  assert (cps.size() < 2);
  if (cps.empty())
    cps.push_back (internal->new_unit_clause (lit, true));
  proof.push_back (bc);
  Clause * cp = cps[0];
  assert (cp);
  if (r && r->size == 1) assert (cp == r);
  else if (!r) internal->var(lit).reason = cp;
  assert (counterparts[bc].size() == 1);
  assert (cp->literals[0] == lit);
  assert (internal->var(lit).reason->literals[0] == lit);
  STOP (bchecking);
}

void BChecker::add_derived_empty_clause () {
  if (inconsistent) return;
  START (bchecking);
  LOG (c, "BCHECKER derived clause notification");
  stats.derived++;
  inconsistent = true;
  STOP (bchecking);
}

void BChecker::delete_clause (Clause * c) {
  if (inconsistent) return;
  START (bchecking);
  LOG (c, "BCHECKER clause deletion notification");
  {
    // Original clauses are not being cached and might be deleted by the internal solver.
    // Therefore, if the clause isn't in bchecker db, it has to be an original clause.
    ///TODO: Consider caching original clauses too so it would be possible to assert
    // that deleted clauses do exist as a sanity check.
  }
  if (num_clauses) {
    BCheckerClause ** p = find (c), * d = *p;
    if (d) {
      stats.deleted++;
      auto it = std::find(counterparts[d].begin(), counterparts[d].end(), c);
      assert (d->size);
      {
        ///BUG: Internal solver isn't tracking allocated clauses of size 1.
        // However, it does notify the proof when these clauses should be
        // removed. Since the observer does track these clauses, it can delete them.
        // The problem is that calling mark_garbage will result in a loop of calls
        // where the assertion for internal->clauses to be empty is violated.

        // if (d->counterpart->size == 1)
          // internal->mark_garbage (d->counterpart);
      }
      if (it != counterparts[d].end()) {
        counterparts[d].erase (it);
      }
      if (counterparts[d].empty ()) d->garbage = true;
    }
  }
  STOP (bchecking);
}

/*------------------------------------------------------------------------*/

void BChecker::update_moved_counterparts () {
  if (inconsistent) return;
  START (bchecking);
  for (auto & pair : counterparts) {
    BCheckerClause * bc = pair.first;
    for (int i = 0; i < pair.second.size(); i++) {
      Clause * c = pair.second[i];
      assert (c);
      assert (c->size == 2 || !c->garbage || c->moved);
      if (c->moved) {
        assert (c->copy);
        /// TODO: proof isn't notified with deleted clauses
        //  of size 2 until they are actually deallocated.
        // Consider cancelling the delaying when bchecking.
        if (c->size != 2)
          assert (!c->copy->garbage);
        pair.second[i] = c->copy;
      }
      assert (unsigned(c->size) == bc->size);
    }
  }
  STOP (bchecking);
}

/*------------------------------------------------------------------------*/

void BChecker::dump () {
  int max_var = 0;
  for (uint64_t i = 0; i < size_clauses; i++)
    for (BCheckerClause * c = clauses[i]; c; c = c->next)
      for (unsigned i = 0; i < c->size; i++)
        if (abs (c->literals[i]) > max_var)
          max_var = abs (c->literals[i]);
  printf ("p cnf %d %" PRIu64 "\n", max_var, num_clauses);
  for (uint64_t i = 0; i < size_clauses; i++)
    for (BCheckerClause * c = clauses[i]; c; c = c->next) {
      for (unsigned i = 0; i < c->size; i++)
        printf ("%d ", c->literals[i]);
      printf ("0\n");
    }
}

}
