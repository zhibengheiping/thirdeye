-module(te0).

-export(
   [th1/1, prove_th1/1]).

-import(te, [mp/2]).

a1(T, R, S) ->
    ['⊦', [[[S, R, '='],
            [S, T, '='],
            '→'],
           [R, T, '='],
           '→']].

a2(T) ->
    ['⊦', [T, ['0', T, '+'], '=']].

th1(T) ->
    ['⊦', [T, T, '=']].

prove_th1(T) ->
    P1 = a1(['0', T, '+'], T, T),
    P2 = a2(T),
    P3 = mp(P1, P2),
    P4 = mp(P3, P2),
    P4.
