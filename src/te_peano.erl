-module(te_peano).

-export(
   ['0+0=0'/0, 'prove_0+0=0'/0]).

-import(te, [mp/2]).

binop_imply() ->
    ['⊦', [binop, '→']].

binop_iff() ->
    ['⊦', [binop, '⇔']].

iff(P, Q) ->
    ['⊦', [[P, '→', Q], '→', [[Q, '→', P], '→', [P, '⇔', Q]]]].

iff_left(P, Q) ->
    ['⊦', [[P, '⇔', Q], '→', [P, '→', Q]]].

iff_right(P, Q) ->
    ['⊦', [[P, '⇔', Q], '→', [Q, '→', P]]].

binop_eq() ->
    ['⊦',[binop, '=']].

eq_comm(P, Q) ->
    ['⊦', [[P, '=', Q], '→', [Q, '=', P]]].

eq_trans(P, Q, R) ->
    ['⊦', [[P, '=', Q], '→', [[Q, '=', R], '→', [P, '=', R]]]].

unop_id() ->
    ['⊦',[unop, id]].

id(X) ->
    ['⊦', [[id, X], '=', X]].

forall_inst_unop(P, X) ->
    ['⊦', [[unop, P], '→', [['∀', P], '→', [P, X]]]].

forall_inst_binop(P, X, Y) ->
    ['⊦', [[binop, P], '→', [['∀', P], '→', [X, P, Y]]]].

binop_compose() ->
    ['⊦',[binop, '∘']].

binop_left() ->
    ['⊦',[binop, '⊣']].

binop_right() ->
    ['⊦',[binop, '⊢']].

left(X, Y) ->
    ['⊦', [[X, '⊣', Y], '=', X]].

right(X, Y) ->
    ['⊦', [[X, '⊢', Y], '=', Y]].

unop_bind_left(O, X) ->
    ['⊦', [[binop, O], '→', [unop, ['_', O, X]]]].

unop_bind_right(O, X) ->
    ['⊦', [[binop, O], '→', [unop, [X, O, '_']]]].

bind_left(O, X, Y) ->
    ['⊦', [[binop, O], '→', [[['_', O, Y], X], '=', [X, O, Y]]]].

bind_right(O, X, Y) ->
    ['⊦', [[binop, O], '→', [[[X, O, '_'], Y], '=', [X, O, Y]]]].

unop_fork(P, Q, R) ->
    ['⊦', [[unop, P], '→', [[binop, Q], '→', [[unop, R], '→', [unop, [fork, P, Q, R]]]]]].

binop_fork(P, Q, R) ->
    ['⊦', [[binop, P], '→', [[binop, Q], '→', [[binop, R], '→', [binop, [fork, P, Q, R]]]]]].

fork_unop(P, Q, R, X) ->
    ['⊦', [[unop, P], '→', [[binop, Q], '→', [[unop, R], '→', [[[fork, P, Q, R], X], '⇔', [[P, X], Q, [R, X]]]]]]].

fork_binop(P, Q, R, X, Y) ->
    ['⊦', [[binop, P], '→', [[binop, Q], '→', [[binop, R], '→', [[X, [fork, P, Q, R], Y], '⇔', [[X, P, Y], Q, [X, R, Y]]]]]]].

unop_natp() ->
    ['⊦',[unop, natp]].

natp_0() ->
    ['⊦', [natp, '0']].

unop_succ() ->
    ['⊦',[unop, succ]].

natp_succ(X) ->
    ['⊦', [[natp, X], '→', [natp, [succ, X]]]].

binop_plus() ->
    ['⊦',[binop, '+']].

add_0() ->
    ['⊦', ['∀', [fork, natp, '→', [fork, ['_', '+', '0'], '=', id]]]].

add_succ() ->
    ['⊦', ['∀', [fork, [natp, '∘', '⊣'], '→', [fork, [natp, '∘', '⊢'], '→', [fork, [fork, '⊣', '+', [succ, '∘', '⊢']], '=', [succ, '∘', '+']]]]]].

nat_ind([unop, P]) ->
    ['⊦', [[unop, P], '→',
           [[P, '0'],
            '→',
            [['∀', [fork, natp, '→', [fork, P, '→', [P, '∘', succ]]]],
             '→',
             ['∀', [fork, natp, '→', P]]]]]].


'0+0=0'() ->
    ['⊦', [['0', '+', '0'], '=', '0']].

'prove_0+0=0'() ->
    T0 = '0',
    T1 = '+',
    T2 = [T0, T1, T0],
    T3 = id,
    T4 = [T3, T0],
    T5 = '_',
    T6 = [T5, T1, T0],
    T7 = [T6, T0],
    T8 = fork,
    T9 = '=',
    T10 = [T8, T6, T9, T3],
    T11 = [T10, T0],
    T12 = [T7, T9, T4],
    T13 = natp,
    T14 = '→',
    T15 = [T8, T13, T14, T10],
    T16 = [T15, T0],
    T17 = [T13, T0],
    T18 = [T17, T14, T11],

    P0 = eq_trans(T2, T4, T0),
    P1 = eq_trans(T2, T7, T4),
    P2 = eq_comm(T7, T2),
    P3 = bind_left(T1, T0, T0),
    P4 = binop_plus(),
    P5 = mp(P3, P4),
    P6 = mp(P2, P5),
    P7 = mp(P1, P6),
    P8 = iff_left(T11, T12),
    P9 = fork_unop(T6, T9, T3, T0),
    P10 = unop_bind_left(T1, T0),
    P11 = mp(P10, P4),
    P12 = mp(P9, P11),
    P13 = binop_eq(),
    P14 = mp(P12, P13),
    P15 = unop_id(),
    P16 = mp(P14, P15),
    P17 = mp(P8, P16),
    P18 = iff_left(T16, T18),
    P19 = fork_unop(T13, T14, T10, T0),
    P20 = unop_natp(),
    P21 = mp(P19, P20),
    P22 = binop_imply(),
    P23 = mp(P21, P22),
    P24 = unop_fork(T6, T9, T3),
    P25 = mp(P24, P11),
    P26 = mp(P25, P13),
    P27 = mp(P26, P15),
    P28 = mp(P23, P27),
    P29 = mp(P18, P28),
    P30 = forall_inst_unop(T15, T0),
    P31 = unop_fork(T13, T14, T10),
    P32 = mp(P31, P20),
    P33 = mp(P32, P22),
    P34 = mp(P33, P27),
    P35 = mp(P30, P34),
    P36 = add_0(),
    P37 = mp(P35, P36),
    P38 = mp(P29, P37),
    P39 = natp_0(),
    P40 = mp(P38, P39),
    P41 = mp(P17, P40),
    P42 = mp(P7, P41),
    P43 = mp(P0, P42),
    P44 = id(T0),
    P45 = mp(P43, P44),
    P45.
