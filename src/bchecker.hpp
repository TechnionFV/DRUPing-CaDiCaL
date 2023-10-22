#ifndef _bchecker_hpp_INCLUDED
#define _bchecker_hpp_INCLUDED

#include "observer.hpp"
#include "unordered_map"

namespace CaDiCaL {

/*-----------------------------------------------------------------------------------

Bchecker implements an offline backward DRUP-based proof validation, interpolants and
core extraction enabled by 'opts.bcheck'.

This code implements the algorithm introduced in the paper "DRUPing For Interpolant"
by Arie Gurfinkel and Yakir Vizel.

Limitations:
  - Allowing other proof observers/checkers in parallel:
    During validation/trimming procedure, bchecker can delete or revive clauses that
    other Internal::Proof observers aren't aware of them. As a result, enabling such
    observers might trigger errors such as deleting a clause that isn't in the proof.

  - Chronological backtracking enabled by 'opts.chrono':
    The combination of chronological backtracking with the algorithm is challenging
    since invariants classically considered crucial to CDCL cease to hold.
    In its current implementation, the algorithm relies on the level order invariant
    that ensures the literals are ordered on the assignment trail in ascending order
    with respect to their decision level.
    In the interest of compatibility with chronological backtracking, adjustments to
    the implementation will be considered in the future.

  // - Not all processing techniques are compatible with this feature:

-----------------------------------------------------------------------------------*/

class Clause;

class BCheckerClause {
public:
  bool marked_garbage;
  int revive_at;
  bool failed;
  bool deleted;
  Clause * counterpart;
  vector<int> literals;
  BCheckerClause (vector<int> c);
  BCheckerClause (Clause * c);
  ~BCheckerClause () = default;
  bool unit () const {
    return literals.size () == 1;
  }
};

class Order {
  int i;
public:
  Order () : i (-1) {}
  bool cached () const { return i >= 0; }
  int cache (int i_) {
    assert (!cached () && i_ >= 0);
    i = i_;
  }
  int evacuate () {
    assert (cached ());
    int i_ = i;
    i = -1;
    return i_;
  }
};

struct lock_scope {
  bool & key;
  lock_scope (bool & key_) : key (key_) { assert (!key_); key = true; };
  ~lock_scope () { key = false; }
};

template<class T>
struct save_scope {
    T& key;
    T initial;
    save_scope(T& key_) : key(key_), initial(key_) { };
    save_scope(T& key_, T val_within_scope) : key(key_), initial(key_) {
      key = val_within_scope;
    };
    ~save_scope() { key = initial; };
};

class BChecker {

  Internal * internal;

  // stack of clausal proof
  //
  vector<BCheckerClause *> proof;

  // for each counterpart 'cp', 'cp_ordering[cp]' contains matching stack index
  //
  unordered_map<Clause *, Order> cp_ordering;

  // stack containig clauses of size 1
  //
  vector<Clause *> unit_clauses;
  Clause * new_unit_clause (const int lit, bool original);

  Clause * failed_constraint;
  bool core_units;
  bool isolate;
  bool validating;

  vector<BCheckerClause *> bchecker_clauses;
  BCheckerClause * insert (Clause *);
  BCheckerClause * insert (const vector<int> &);

  bool trivially_satisfied (const vector <int> & c);
  void append_lemma (BCheckerClause * bc, Clause * c, bool deleted);
  void append_failed (const vector<int>  & c);
  void revive_internal_clause (int);
  void stagnate_internal_clause (const int);
  void reactivate_fixed (int);
  void reactivate_eliminated (int);

  void shrink_internal_trail (const unsigned);
  void clear_conflict ();

  void undo_trail_literal (int);
  void undo_trail_core (Clause * c, unsigned & trail_sz);
  bool is_on_trail (Clause *);

  void mark_core (Clause *);
  void mark_conflict_lit (int l);
  void mark_conflict (bool overconstarined);
  void mark_failed_conflict ();

  void assume_negation (const Clause *);
  bool propagate_conflict ();
  void conflict_analysis_core ();

  void mark_core_trail_antecedents ();
  void unmark_core_clauses ();
  void restore_trail ();
  void clear_failing_assumptions (const unsigned);
  void reallocate ();
  void reconsruct (unsigned);

  void check_environment () const;
  void dump_clauses (bool active = false) const;
  void dump_clause (const Clause *) const;
  void dump_clause (const BCheckerClause *) const;
  void dump_clause (const vector <int> &) const;
  void dump_proof () const;
  void dump_trail () const;
  void dump_core () const;
  bool assert_core_is_unsat () const;

  struct {

    int64_t derived;            // number of added derived clauses
    int64_t deleted;            // number of deleted clauses
    int64_t counterparts;       // number of counterpart references
    int64_t units;              // number of unit clauses allcoated
    int64_t core;               // number of core clauses in current phase
    vector<int64_t> cores;      // number of core clauses for each phase

    void save_core_phase () {
      cores.push_back (core);
    }
  } stats;

public:

  BChecker (Internal *, bool core_units = 0);
  ~BChecker ();

  bool setup_options ();

  void add_derived_clause (Clause *);
  void add_derived_unit_clause (const int, bool original = false);
  void add_derived_empty_clause ();

  void add_failing_assumption (const vector<int> &);

  void strengthen_clause (Clause * c, int lit);
  void flush_clause (Clause *);

  void delete_clause (const vector<int> &, bool original = false);
  void delete_clause (Clause *);

  void update_moved_counterparts ();

  bool trim (bool overconstrained = false);

  void print_stats ();
};

}

#endif
