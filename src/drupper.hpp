#ifndef _drupper_hpp_INCLUDED
#define _drupper_hpp_INCLUDED

#include "observer.hpp"
#include "unordered_map"

namespace CaDiCaL {

/*-----------------------------------------------------------------------------------

The code implements the algorithm introduced in "DRUPing For Interpolant", a paper by
  Arie Gurfinkel and Yakir Vizel. Drupper allows DRUP-based proof trimming, validation,
  interpolants and core extraction enabled by 'opts.drup'.

Limitations:
  - Allowing other proof observers/checkers in parallel:
    During validation/trimming procedure, drupper can delete or revive clauses that
    other Internal::Proof observers aren't aware of. As a result, enabling such
    observers and checkers in parallel might trigger errors.

  - Chronological backtracking enabled by 'opts.chrono':
    The combination of chronological backtracking with the algorithm is challenging
    since invariants classically considered crucial to CDCL cease to hold.
    In its current implementation, the algorithm relies on the level order invariant
    which ensures the literals are ordered on the assignment trail in ascending order
    with respect to their decision level. This invariant is violated.
    In the interest of compatibility with chronological backtracking, adjustments to
    the implementation will be considered in the future.

  - Not all [in/pre]processing techniques are compatible with this feature:
    1) probing / advanced probing / lookahead: isn't resolution based.
    2) conditioning: is this another version of BCE (Bounded Clause Elimination)?
    3) compacting: this feature is not compatible.
       * drupper will revive clauses with wrong mapping.
       * fixed literals are literals that drupper wants to keep.
       * even if we disable reducing/garbage collection ... would this be still be worth it?
    4) subsuming: ok (at least empirically) but does it even work without vivcation? I think so...
    5) vivication: changes order of literals (violated reason_of_lit[0] == lit).
    6) eliminating: problem with - learn_empty_clause (). Passed validation but need to correctly mark core

  - Disable propagating binary clauses as soon as they are marked as garbage.

-----------------------------------------------------------------------------------*/

class Clause;

class DrupperClause {
public:
  bool marked_garbage;
  int revive_at;
  bool failed;
  bool deleted;
  Clause * counterpart;
  vector<int> literals;
  DrupperClause (vector<int> c);
  DrupperClause (Clause * c);
  ~DrupperClause () = default;
  bool unit () const;
};

class Order {
  int i;
public:
  Order () : i (-1) {}
  bool cached () const { return i >= 0; }
  void cache (int i_) {
    assert (!cached () && i_ >= 0);
    i = i_;
  }
  int remove () {
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

class Drupper {

  Internal * internal;

  // stack of clausal proof
  //
  vector<DrupperClause *> proof;

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
  File * file;

  vector<DrupperClause *> drupper_clauses;
  DrupperClause * insert (Clause *);
  DrupperClause * insert (const vector<int> &);

  void set_counterpart (DrupperClause * dc, Clause * c);
  void reset_counterpart (DrupperClause *);

  bool trivially_satisfied (const vector <int> & c);
  void append_lemma (DrupperClause * dcפ, Clause * c, bool deleted);
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
  void dump_clause (const DrupperClause *) const;
  void dump_clause (const vector <int> &) const;
  void dump_proof () const;
  void dump_trail () const;

  bool core_is_unsat () const;
  void dump_core () const;


  struct {

    int64_t derived;            // number of added derived clauses
    int64_t deleted;            // number of deleted clauses
    int64_t counterparts;       // number of counterpart references
    int64_t units;              // number of unit clauses allcoated
    int64_t core;               // number of core clauses in current phase
    vector<int64_t> cores;      // number of core clauses for each phase

  } stats;

  void save_core_phase_stats () {
    stats.cores.push_back (stats.core);
  }

public:

  Drupper (Internal *, File * f = 0, bool core_units = 0);
  ~Drupper ();

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
