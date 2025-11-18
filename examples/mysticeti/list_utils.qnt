// -*- mode: Bluespec; -*-

/**
 * List utility functions for Mysticeti Choreo
 *
 * Provides sorting and filtering utilities for lists.
 * Quint's standard library has limited list operations, so we implement them here.
 *
 * Yassine & Claude Code, 2025
 */
module list_utils {
  import types.* from "./types"

  /**
   * Sort a list of decisions using a comparison function
   * Returns sorted list in ascending order according to less_than predicate
   *
   * Uses insertion sort algorithm for simplicity
   */
  pure def sort_decisions(lst: List[Decision], less_than: (Decision, Decision) => bool): List[Decision] = {
    // Insertion sort implementation
    range(0, lst.length()).foldl(List(), (sorted, i) => {
      val elem = lst[i]
      // Find insertion position
      val pos = range(0, sorted.length()).foldl(sorted.length(), (insert_at, j) => {
        if (j < insert_at and less_than(elem, sorted[j])) j else insert_at
      })
      // Insert at position
      sorted.slice(0, pos).append(elem).concat(sorted.slice(pos, sorted.length()))
    })
  }

  /**
   * Take elements from list while predicate holds
   * Returns a prefix of the list up to (but not including) the first element that fails the predicate
   */
  pure def take_while(lst: List[Decision], pred: Decision => bool): List[Decision] = {
    val stop_idx = range(0, lst.length()).foldl(lst.length(), (stop, i) => {
      if (i < stop and not(pred(lst[i]))) i else stop
    })
    lst.slice(0, stop_idx)
  }

  /**
   * Convert a list to a set
   */
  pure def list_to_set(lst: List[Decision]): Set[Decision] = {
    range(0, lst.length()).foldl(Set(), (acc, i) => acc.union(Set(lst[i])))
  }

  /**
   * Filter a list using a predicate
   * (Quint has .select but this provides consistency with our naming)
   */
  pure def filter_list(lst: List[Decision], pred: Decision => bool): List[Decision] = {
    lst.select(pred)
  }
}
