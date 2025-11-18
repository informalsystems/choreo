// -*- mode: Bluespec; -*-

/**
 * Basic spells - reusable operators for Quint
 */
module basicSpells {
  import option.* from "./option"

  /// An annotation for writing preconditions.
  pure def require(cond: bool): bool = cond

  pure def setRemove(__set: Set[a], __elem: a): Set[a] = {
    __set.exclude(Set(__elem))
  }

  pure def setAdd(__set: Set[a], __elem: a): Set[a] = {
    __set.union(Set(__elem))
  }

  /// Transform values in a map while preserving keys
  pure def transformValues(__map: a -> b, __f: b => c): a -> c = {
    __map.keys().mapBy(k => __f(__map.get(k)))
  }

  /// Map a set via a function, collecting only `Some` results
  pure def filterMap(__set: Set[a], __f: a => Option[b]): Set[b] = {
    __set.fold(Set(), (acc, elem) => {
      match __f(elem) {
        | Some(value) => acc.setAdd(value)
        | None => acc
      }
    })
  }
}
