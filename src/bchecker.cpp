#include "internal.hpp"
#include "unordered_set"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

BChecker::BChecker (Internal * i)
:
  internal (i), inconsistent (false), num_clauses (0),
  num_garbage (0), size_clauses (0), clauses (0)

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
  res->core = false;
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

void BChecker::undo_trail_core (Clause * c, int & trail_sz) {
  LOG ("BCHECKER undoing trail core");
  assert (trail_sz > 0 && c->size > 0);
  int clit = c->literals[0];
  size_t count = 0;
  while (internal->trail[trail_sz - 1] != clit)
  {
    assert(trail_sz > 0);
    int l = internal->trail[--trail_sz];
    if (!internal->active (l)) continue;
    assert (internal->val (l) > 0);
    assert (internal->val (-l) < 0);
    Var v = internal->var (l);
    assert (v.level > 0);
    Clause * r = v.reason;
    if (!r) continue;
    assert (r->literals[0] == clit); // If this fails we can't rely on this convertion as in Minsiat.

    ///TODO: internal->unassign method is exclusive for backtracking facilities. Need to undoo its inlining...
    // internal->unassign (l);

    /// TODO:|NOTE: In Minisat patch, the following code block is guarded
    //  by if (core_units) so might need to do this here as well.
    r->core = true;

    // Antecedents of any core literal on the trail are marked as core as well.
    for (int j = 1; j < r->size; j++)
    {
      Var x = internal->var(r->literals[j]);
      assert(x.reason);
      x.reason->core = true;
    }
    count++;
  }
  assert(clit == internal->trail[trail_sz - 1]);
  ///TODO: internal->unassign method is exclusive for backtracking facilities. Need to undoo its inlining...
  // internal->unassign (internal->trail[--trail_sz]);
  LOG ("BCHECKER %zd literals have been popped from the trail", count+1);
  internal->trail.resize(trail_sz);
  /// TODO: What should internal->control[1].count be here? This might affect analyze. (before 0 and after 0, I guess).
  internal->control[1].trail = internal->trail.size ();
}

bool BChecker::is_on_trail (Clause * c) {
 assert (c);
 return c->reason;
}

bool BChecker::validate_lemma (Clause * c) {
  return true;
}

bool BChecker::validate () {
  assert (inconsistent);
  assert (proof.size ());

  ///TODO: Handle case where there are conflicting assumptions.

  /// TODO: Do we need to protect_reasons (); here?

  Clause * top; // assume that this is the Clause reference of proof.back ();
  top->core = true;

  internal->backtrack();
  int trail_sz = internal->trail.size();

  /// TODO: Set 'internal->level' appropriately all over the place!
  for (int i = proof.size() - 2; i >= 0; i--) {
    BCheckerClause * bc = proof[i];
    assert(bc && bc->size);
    Clause * c = 0;
    // revive if deleted.
    if (bc->garbage) {
      ///TODO: It means c is deleted from the internal solver database.
      //         - Allocate a new Clause object with c in the internal solver database (Assign it to 'c').
      //         - Order the new clause's literals.
      //         - Updarte the bchecker clause object accordingly.
      //         - If c is a  unit clause, then:
      //           -- Enqueue to propagate on it in the internal solver
      //              with the new allocated reference as the reason clause.
      //              --- internal->search_assign_driving (c->literals[0], <new reference>);
      ///TODO: Update bc->counterpart accordingle
      assert (!bc->counterpart);
      c = bc->counterpart = internal->new_clause (false);
    } else {
      ///TODO: If clause isn't deleted, bc->counterpart must be valid pointer. Assign it to 'c'.
      assert (bc->counterpart);
      c = bc->counterpart;
    }

    assert (c && bc->counterpart == c && !bc->garbage);

    if (is_on_trail (c)) {
      /// TODO: In Minisat patch, this is guarded by if (core_units)
      //  so might need to do this here as well.
      c->core = true;

      /// TODO: Assert that the literal which its antecedent is c is at c[0] all over the place!
      undo_trail_core (c, trail_sz);

      // delete it.
      if (c->size > 1) {
        bc->garbage = true;
        bc->core = false;
        internal->mark_garbage (c);
      }

      if (c->core) {
        assert (!internal->val (c->literals[0]));
        /// TODO: This should be conditioned with 'if (not initial clause)'. (According to the paper at least).
        if (!validate_lemma (c))
          return false;
      }
    }
  }

  /// TODO: find core clauses in the rest of the trail.
  /// TODO: Put units back on the trail.
  /// TODO: Flush watches
  return true;
  return false;
}

/*------------------------------------------------------------------------*/

void BChecker::add_derived_clause (const vector<int> & c) {
  if (inconsistent) return;
  START (bchecking);
  LOG (c, "BCHECKER addition of derived clause");
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
  LOG (c, "BCHECKER bchecking deletion of clause");
  stats.deleted++;
  BCheckerClause ** p = find (c), * d = *p;
  if (d) {
    ///EXP:This assertion is relaxed compared to Checker::delete_clause since clauses of size 1 are assumed
    // to be tautology during solve (). Here we aren't checking values if literals during solving.
    // Therefore, we can safely relax this assertion as CaDiCaL might delete clauses of size 1.
    assert (d->size);
    assert (num_clauses);
    num_garbage++;
    d->garbage = 1;
    d->counterpart = 0;
  } else {
    /// TODO:: If the clause hasn't been found, it has to be an original clause.
    //         Cadical might delete an orginal clause and mark a new one as derived if it simplifies the original clause
    //         by removing duplicated/falsified literals.
    //         1 - Assert it is safe to treat there clauses as learnt clauses.
    //         2 - Consider caching the original formula and asserting deleted clauses do exist.
  }
  STOP (bchecking);
}

void BChecker::cache_counterpart (Clause * c) {
  if (inconsistent) return;
  START (bchecking);
  LOG (c, "BCHECKER storing counterpart");
  assert (proof.size ());
  BCheckerClause * bc = proof.back ();
  assert (bc);
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
      printf ("%d ", c->core);
      for (unsigned i = 0; i < c->size; i++)
        printf ("%d ", c->literals[i]);
      printf ("0\n");
    }
}

}
