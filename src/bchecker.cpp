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
  res->hash = hash;
  res->size = size;
  res->core = 0;
  res->garbage = 0;
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

bool BChecker::validate () {
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
  } else {
    /// TODO:: If the clause hasn't been found, it has to be an original clause.
    //         Cadical might delete an orginal clause and mark a new one as derived if it simplifies the original clause
    //         by removing duplicated/falsified literals.
    //         1 - Assert it is safe to treat there clauses as learnt clauses.
    //         2 - Consider caching the original formula and asserting deleted clauses do exist.
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
      printf ("%d ", c->core);
      for (unsigned i = 0; i < c->size; i++)
        printf ("%d ", c->literals[i]);
      printf ("0\n");
    }
}

}
