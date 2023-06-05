#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

inline unsigned BChecker::l2u (int lit) {
   assert (lit);
   assert (lit != INT_MIN);
   unsigned res = 2*(abs (lit) - 1);
   if (lit < 0) res++;
   return res;
}

inline signed char BChecker::val (int lit) {
  assert (lit);
  assert (lit != INT_MIN);
  assert (abs (lit) < size_vars);
  assert (vals[lit] == -vals[-lit]);
  return vals[lit];
}

signed char & BChecker::mark (int lit) {
  const unsigned u = l2u (lit);
  assert (u < marks.size ());
  return marks[u];
}

inline BCheckerWatcher & BChecker::watcher (int lit) {
  const unsigned u = l2u (lit);
  assert (u < watchers.size ());
  return watchers[u];
}

/*------------------------------------------------------------------------*/

BCheckerClause * BChecker::new_clause () {
  const size_t size = simplified.size ();
  /// TODO: Need to log learnt unit clauses as well.
  //  Fix this assert once this is handled in code.
  assert (size > 1), assert (size <= UINT_MAX);
  const size_t bytes = sizeof (BCheckerClause) + (size - 2) * sizeof (int);
  BCheckerClause * res = (BCheckerClause *) new char [bytes];
  res->next = 0;
  res->hash = last_hash;
  res->size = size;
  res->core = false;
  res->garbage = false;
  int * literals = res->literals, * p = literals;
  for (const auto & lit : simplified)
    *p++ = lit;
  num_clauses++;

  // First two literals are used as watches and should not be false.
  //
  for (unsigned i = 0; i < 2; i++) {
    int lit = literals[i];
    if (!val (lit)) continue;
    for (unsigned j = i + 1; j < size; j++) {
      int other = literals[j];
      if (val (other)) continue;
      swap (literals[i], literals[j]);
      break;
    }
  }
  assert (!val (literals [0]));
  assert (!val (literals [1]));
  watcher (literals[0]).push_back (BCheckerWatch (literals[1], res));
  watcher (literals[1]).push_back (BCheckerWatch (literals[0], res));

  return res;
}

void BChecker::delete_clause (BCheckerClause * c) {
  if (c->size) {
    assert (c->size > 1);
    assert (num_clauses);
    num_clauses--;
  } else {
    assert (num_garbage);
    num_garbage--;
  }
  delete [] (char*) c;
}

void BChecker::enlarge_clauses () {
  assert (num_clauses == size_clauses);
  const uint64_t new_size_clauses = size_clauses ? 2*size_clauses : 1;
  LOG ("BCHECKER enlarging clauses of bchecker from %" PRIu64 " to %" PRIu64,
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

bool BChecker::clause_satisfied (BCheckerClause * c) {
  for (unsigned i = 0; i < c->size; i++)
    if (val (c->literals[i]) > 0)
      return true;
  return false;
}

/*------------------------------------------------------------------------*/

BChecker::BChecker (Internal * i)
:
  internal (i),
  size_vars (0), vals (0),
  inconsistent (false), num_clauses (0), num_garbage (0),
  size_clauses (0), clauses (0),
  next_to_propagate (0), last_hash (0)
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

  memset (&stats, 0, sizeof (stats));           // Initialize statistics.
}

BChecker::~BChecker () {
  LOG ("BCHECKER delete");
  vals -= size_vars;
  delete [] vals;
  for (size_t i = 0; i < size_clauses; i++)
    for (BCheckerClause * c = clauses[i], * next; c; c = next)
      next = c->next, delete_clause (c);
  delete [] clauses;
}

/*------------------------------------------------------------------------*/

// The simplicity for accessing 'vals' and 'watchers' directly through a
// signed integer literal, comes with the price of slightly more complex
// code in deleting and enlarging the bchecker data structures.

void BChecker::enlarge_vars (int64_t idx) {

  assert (0 < idx), assert (idx <= INT_MAX);

  int64_t new_size_vars = size_vars ? 2*size_vars : 2;
  while (idx >= new_size_vars) new_size_vars *= 2;
  LOG ("BCHECKER enlarging variables of bchecker from %" PRId64 " to %" PRId64 "",
    size_vars, new_size_vars);

  signed char * new_vals;
  new_vals = new signed char [ 2*new_size_vars ];
  clear_n (new_vals, 2*new_size_vars);
  new_vals += new_size_vars;
  if (size_vars) // To make sanitizer happy (without '-O').
    memcpy ((void*) (new_vals - size_vars),
            (void*) (vals - size_vars), 2*size_vars);
  vals -= size_vars;
  delete [] vals;
  vals = new_vals;

  watchers.resize (2*new_size_vars);
  marks.resize (2*new_size_vars);

  assert (idx < new_size_vars);
  size_vars = new_size_vars;
}

inline void BChecker::import_literal (int lit) {
  assert (lit);
  assert (lit != INT_MIN);
  int idx = abs (lit);
  if (idx >= size_vars) enlarge_vars (idx);
  simplified.push_back (lit);
  unsimplified.push_back (lit);
}

void BChecker::import_clause (const vector<int> & c) {
  for (const auto & lit : c)
    import_literal (lit);
}

struct lit_smaller {
  bool operator () (int a, int b) const {
    int c = abs (a), d = abs (b);
    if (c < d) return true;
    if (c > d) return false;
    return a < b;
  }
};

/// TODO: Should we really discard tautological clauses among proof validation?
bool BChecker::tautological () {
  sort (simplified.begin (), simplified.end (), lit_smaller ());
  const auto end = simplified.end ();
  auto j = simplified.begin ();
  int prev = 0;
  for (auto i = j; i != end; i++) {
    int lit = *i;
    if (lit == prev) continue;          // duplicated literal
    if (lit == -prev) return true;      // tautological clause
    const signed char tmp = val (lit);
    if (tmp > 0) return true;           // satisfied literal and clause
    *j++ = prev = lit;
  }
  simplified.resize (j - simplified.begin ());
  return false;
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

uint64_t BChecker::compute_hash () {
  unsigned i = 0, j = 0;
  uint64_t tmp = 0;
  for (i = 0; i < simplified.size (); i++) {
    int lit = simplified[i];
    tmp += nonces[j++] * (uint64_t) lit;
    if (j == num_nonces) j = 0;
  }
  return last_hash = tmp;
}

BCheckerClause ** BChecker::find () {
  stats.searches++;
  BCheckerClause ** res, * c;
  const uint64_t hash = compute_hash ();
  const unsigned size = simplified.size ();
  const uint64_t h = reduce_hash (hash, size_clauses);
  for (const auto & lit : simplified) mark (lit) = true;
  for (res = clauses + h; (c = *res); res = &c->next) {
    if (c->hash == hash && c->size == size) {
      bool found = true;
      const int * literals = c->literals;
      for (unsigned i = 0; found && i != size; i++)
        found = mark (literals[i]);
      if (found) break;
    }
    stats.collisions++;
  }
  for (const auto & lit : simplified) mark (lit) = false;
  return res;
}

void BChecker::insert () {
  stats.insertions++;
  if (num_clauses == size_clauses) enlarge_clauses ();
  const uint64_t h = reduce_hash (compute_hash (), size_clauses);
  BCheckerClause * c = new_clause ();
  c->next = clauses[h];
  clauses[h] = c;
}

/*------------------------------------------------------------------------*/

inline void BChecker::assign (int lit) {
  assert (!val (lit));
  vals[lit] = 1;
  vals[-lit] = -1;
  trail.push_back (lit);
}

inline void BChecker::assume (int lit) {
  signed char tmp = val (lit);
  if (tmp > 0) return;
  assert (!tmp);
  stats.assumptions++;
  assign (lit);
}

bool BChecker::validate () {
  assert (false && "needs to be implemented");
  return false;
}

/*------------------------------------------------------------------------*/

void BChecker::add_clause (const char * type) {
#ifndef LOGGING
  (void) type;
#endif

  int unit = 0;
  for (const auto & lit : simplified) {
    const signed char tmp = val (lit);
    if (tmp < 0) continue;
    assert (!tmp);
    if (unit) { unit = INT_MIN; break; }
    unit = lit;
  }

  if (simplified.empty ()) {
    LOG ("BCHECKER added empty %s clause", type);
    inconsistent = true;
  } if (!unit) {
    LOG ("BCHECKER added and checked falsified %s clause", type);
    inconsistent = true;
  } else if (unit != INT_MIN) {
    LOG ("BCHECKER added and checked %s unit clause %d", type, unit);
    assign (unit);
    stats.units++;
  } else insert ();
}

void BChecker::add_original_clause (const vector<int> & c) {
  if (inconsistent) return;
  START (bchecking);
  LOG (c, "BCHECKER addition of original clause");
  stats.added++;
  stats.original++;
  import_clause (c);
  if (tautological ())
    LOG ("BCHECKER ignoring satisfied original clause");
  else add_clause ("original");
  simplified.clear ();
  unsimplified.clear ();
  STOP (bchecking);
}

void BChecker::add_derived_clause (const vector<int> & c) {
  if (inconsistent) return;
  START (bchecking);
  LOG (c, "BCHECKER addition of derived clause");
  stats.added++;
  stats.derived++;
  import_clause (c);
  if (tautological ())
    LOG ("BCHECKER ignoring satisfied derived clause");
  else add_clause ("derived");
  simplified.clear ();
  unsimplified.clear ();
  STOP (bchecking);
}

/*------------------------------------------------------------------------*/

void BChecker::delete_clause (const vector<int> & c) {
  if (inconsistent) return;
  START (bchecking);
  LOG (c, "BCHECKER bchecking deletion of clause");
  stats.deleted++;
  import_clause (c);
  if (!tautological ()) {
    BCheckerClause ** p = find (), * d = *p;
    if (d) {
      assert (d->size > 1);
      // mark as garbage
      num_garbage++;
    } else {
      fatal_message_start ();
      fputs ("deleted clause not in proof:\n", stderr);
      for (const auto & lit : unsimplified)
        fprintf (stderr, "%d ", lit);
      fputc ('0', stderr);
      fatal_message_end ();
    }
  }
  simplified.clear ();
  unsimplified.clear ();
  STOP (bchecking);
}

}
