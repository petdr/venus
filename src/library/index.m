%------------------------------------------------------------------------------%
% This file may only be copied under the terms of the GNU Library General
% Public License - see the file COPYING.LIB in the Venus distribution.
%------------------------------------------------------------------------------%
:- module index.
:- interface.

:- import_module list.

:- type index(K, V).

:- typeclass index_key(K) where [
    pred smaller_key(K::in, K::out) is semidet
].

:- func init = index(K, V).

:- pred set(K::in, V::in, index(K, V)::in, index(K, V)::out) is det <= index_key(K).

:- pred search(index(K, V)::in, K::in, list(V)::out) is semidet.

:- func lookup(index(K, V), K) = list(V).

:- implementation.

:- import_module map.
:- import_module set.
:- import_module svmap.

:- type index(K, V) == map(K, set(V)).

index.init = map.init.

index.set(K, V, !Index) :-
    ( map.search(!.Index, K, Set0) ->
        Set = set.insert(Set0, V)
    ;
        Set = set.make_singleton_set(V)
    ),
    svmap.set(K, Set, !Index),
    ( smaller_key(K, SmallerK) ->
        index.set(SmallerK, V, !Index)
    ;
        true
    ).

index.search(Index, K, set.to_sorted_list(Vs)) :-
    map.search(Index, K, Vs).

index.lookup(Index, K) =
    ( index.search(Index, K, Vs) ->
        Vs
    ;
        []
    ).
