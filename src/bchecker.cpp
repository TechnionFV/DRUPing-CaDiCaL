#include "internal.hpp"
#include "unordered_set"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

BChecker::BChecker (Internal * i)
:
  internal (i), inconsistent (false), num_clauses (0),
  size_clauses (0), clauses (0)

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
  unsigned i = 0, j = 0;
  uint64_t hash = 0;
  for (i = 0; i < simplified.size (); i++) {
    int lit = simplified[i];
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

BCheckerClause * BChecker::get_bchecker_clause (Clause * c) {
  vector<int> dummy;
  for (int i = 0; i < c->size; i++)
    dummy.push_back (c->literals[i]);
  return get_bchecker_clause (dummy);
}

BCheckerClause * BChecker::get_bchecker_clause (vector<int> & c) {
  if (!num_clauses)
    return insert (c);
  BCheckerClause ** p = find (c);
  assert (p);
  return !(*p) ? insert (c) : *p;
}

/*------------------------------------------------------------------------*/

Clause * BChecker::revive_internal_clause (BCheckerClause * bc) {

  ///TODO: Avoid unnecessary allocations and reuse valid garbage Clause references when possible.

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
    c = bc->counterpart = internal->new_clause (false);
    internal->clause.clear();
    for (int k = 1; k < c->size && internal->val(c->literals[1]); k++)
      if (!internal->val(c->literals[k]))
      {
        int l = c->literals[1];
        c->literals[1] = c->literals[k], c->literals[k] = l;
      }
    internal->watch_clause (c);
  }
  bc->garbage = false;
  return c;
}

void BChecker::stagnate_internal_clause (BCheckerClause * bc) {
  assert (bc && !bc->garbage && bc->counterpart);
  bc->garbage = true;
  if (bc->counterpart->size > 1) {
    internal->unwatch_clause (bc->counterpart);
  }
  internal->mark_garbage (bc->counterpart);
  assert (bc->counterpart->garbage);
}

void  BChecker::shrink_internal_trail (const int trail_sz) {
  internal->trail.resize(trail_sz);
  /// TODO: Set internal->control[1].count correctly if needed.
  if (internal->level) {
    assert(internal->control.size () > 1);
    internal->control[1].trail = internal->trail.size ();
  }
}

void BChecker::undo_trail_core (Clause * c, int & trail_sz) {
  LOG ("BCHECKER undoing trail core");
  assert (trail_sz > 0 && c->size > 0);
  int clit = c->literals[0];
  while (internal->trail[trail_sz - 1] != clit)
  {
    assert(trail_sz > 0);
    int l = internal->trail[--trail_sz];
    if (!internal->active (l)) continue;
    assert (internal->val (l) > 0);
    assert (internal->val (-l) < 0);
    Var & v = internal->var (l);
    assert (v.level > 0);
    Clause * r = v.reason;
    if (!r) continue;
    assert (r->literals[0] == clit);

    internal->unassign (l);

    /// TODO:|NOTE: In Minisat patch, the following code block is guarded
    //  by if (core_units). Do we want to integrate this option here as well? 
    r->core = true;

    for (int j = 1; j < r->size; j++)
    {
      Var & x = internal->var(r->literals[j]);
      assert(x.reason);
      x.reason->core = true;
    }
  }
  assert(clit == internal->trail[trail_sz - 1]);

  { // Sanity check. To be removed later.
    Var v = internal->var (clit);
    assert (v.level > 0);
    Clause * r = v.reason;
    assert (r && r == c);
    assert (r->literals[0] == clit);
  }

  internal->unassign (internal->trail[--trail_sz]);
}

bool BChecker::is_on_trail (Clause * c) {
 assert (c);
 return c->reason;
}

bool BChecker::validate_lemma (Clause * c) {
  return true;
}

void BChecker::mark_core_trail_antecedents () {
  for (const auto & lit : internal->trail)
  {
    Var & x = internal->var (lit);
    if (!x.reason) continue; // internal->assign_unit (int)
    Clause * c = x.reason;
    if (c->core)
    {
      for (int j = 1; j < c->size; ++j)
      {
        Var & x = internal->var(c->literals[j]);
        assert (x.reason);
        x.reason->core = true;
      }
      ///TODO: This was done in Minisat.. but why?
      // qhead = i;
    }
  }
}

void BChecker::check_counterparts () {
  for (uint64_t i = 0; i < size_clauses; i++)
    for (BCheckerClause * bc = clauses[i]; bc; bc = bc->next)
      if (bc->garbage)
        assert (!bc->counterpart);
      else if (bc->counterpart)
          assert (!bc->counterpart->garbage || bc->counterpart->moved);
}

bool BChecker::validate () {
  assert (inconsistent);
  assert (proof.size ());

  ///TODO: Handle case where there are conflicting assumptions
  ///TODO: internal->protect_reasons ();

  check_counterparts ();

  BCheckerClause * bc_top = proof.back ();

  assert (!bc_top->garbage);
  assert (bc_top->counterpart);

  Clause * top = proof.back()->counterpart;
  top->core = true;

  internal->backtrack();
  int trail_sz = internal->trail.size();

  /// TODO: Set 'internal->level' appropriately all over the place!
  for (int i = proof.size() - 2; i >= 0; i--) {
    BCheckerClause * bc = proof[i];
    assert(bc && bc->size);

    Clause * c = nullptr;

    // revive if deleted.
    if (bc->garbage) {
      c = revive_internal_clause (bc);
      assert (!c->garbage);
    } else {
      ///NOTE: If clause isn't deleted, bc->counterpart must be valid pointer.
      if (!bc->counterpart) {
        printf ("%d\n", bc->size);
      }
      assert (bc->counterpart);
      assert (!bc->counterpart->garbage);
      c = bc->counterpart;
    }

    assert (c && bc && !bc->garbage && !c->garbage);
    assert (bc->counterpart == c);

    if (is_on_trail (c)) {
      /// TODO: In Minisat patch, this is guarded by if (core_units). This might need here as well.
      c->core = true;
      undo_trail_core (c, trail_sz);
    }

    stagnate_internal_clause (bc);

    if (c->core) {
      /// TODO: According to the paper, this should be conditioned with 'if not initial clause' ( if (c->redundant) ).
      assert (!internal->val (c->literals[0]));
      shrink_internal_trail (trail_sz);
      if (!validate_lemma (c))
        return false;
    }
  }

  shrink_internal_trail (trail_sz);

  /// TODO: find core clauses in the rest of the trail.
  mark_core_trail_antecedents ();

  /// TODO: Put units back on the trail.

  internal->flush_all_occs_and_watches ();

  ///TODO: Clean up internal clauses that were created for validation purposes.
  return true;
}

/*------------------------------------------------------------------------*/

void BChecker::add_derived_clause (const vector<int> & c) {
  if (inconsistent) return;
  START (bchecking);
  LOG (c, "BCHECKER derived clause notification");
  stats.derived++;
  if (c.empty ())
    inconsistent = true;
  else
    proof.push_back (insert(c));
  STOP (bchecking);
}

void BChecker::delete_clause (const vector<int> & c) {
  if (inconsistent) return;
  START (bchecking);
  LOG (c, "BCHECKER clause deletion notification");
  stats.deleted++;
  {
    // Original clauses are not being cached and might be deleted by the internal solver.
    // Therefore, if the clause doesn't exist in bchecker db, it has to be an original clause.
    ///TODO: Consider caching original clauses too so it would be possible to assert that
    // deleted clauses do exist as a sanity check.
  }
  if (num_clauses) {
    BCheckerClause ** p = find (c), * d = *p;
    if (d) {
      assert (!d->garbage && d->size);
      d->garbage = true;
      d->counterpart = 0;
    }
  }
  STOP (bchecking);
}

void BChecker::cache_counterpart (Clause * c) {
  if (inconsistent) return;
  START (bchecking);
  LOG (c, "BCHECKER caching clause counterpart");
  stats.counterparts++;
  assert (proof.size ());
  BCheckerClause * bc = proof.back ();
  assert (bc && !bc->counterpart);
  bc->counterpart = c;
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
