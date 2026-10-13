-module(te_peano).

-export(
   ['0+0=0'/0, 'prove_0+0=0'/0]).

mp(['⊦', P], ['⊦', [P, '→', Q]]) ->
    ['⊦', Q].

unop([unop, O], [term, X]) ->
    [term, [O, X]].

binop([binop, O], [term, X], [term, Y]) ->
    [term, [X, O, Y]].

binop_imply() ->
    [binop, '→'].

binop_iff() ->
    [binop, '⇔'].

iff([term, P], [term, Q]) ->
    ['⊦', [[P, '→', Q], '→', [[Q, '→', P], '→', [P, '⇔', Q]]]].

iff_left([term, P], [term, Q]) ->
    ['⊦', [[P, '⇔', Q], '→', [P, '→', Q]]].

iff_right([term, P], [term, Q]) ->
    ['⊦', [[P, '⇔', Q], '→', [Q, '→', P]]].

binop_eq() ->
    [binop, '='].

eq_comm([term, P], [term, Q]) ->
    ['⊦', [[P, '=', Q], '→', [Q, '=', P]]].

eq_trans([term, P], [term, Q], [term, R]) ->
    ['⊦', [[P, '=', Q], '→', [[Q, '=', R], '→', [P, '=', R]]]].

unop_id() ->
    [unop, id].

id([term, X]) ->
    ['⊦', [[id, X], '=', X]].

unop_forall() ->
    [unop, '∀'].

binop_forall() ->
    [binop, '∀'].

forall_inst_unop([unop, P], [term, X]) ->
    ['⊦', [['∀', P], '→', [P, X]]].

forall_inst_binop([binop, P], [term, X], [term, Y]) ->
    ['⊦', [['∀', P], '→', [X, P, Y]]].

binop_compose() ->
    [binop, '∘'].

binop_left() ->
    [binop, '⊣'].

binop_right() ->
    [binop, '⊢'].

left([term, X], [term, Y]) ->
    ['⊦', [[X, '⊣', Y], '=', X]].

right([term, X], [term, Y]) ->
    ['⊦', [[X, '⊢', Y], '=', Y]].

unop_bind_left([binop, O], [term, X]) ->
    [unop, ['_', O, X]].

unop_bind_right([binop, O], [term, X]) ->
    [unop, [X, O, '_']].

bind_left([binop, O], [term, X], [term, Y]) ->
    ['⊦', [[['_', O, Y], X], '=', [X, O, Y]]].

bind_right([binop, O], [term, X], [term, Y]) ->
    ['⊦', [[[X, O, '_'], Y], '=', [X, O, Y]]].

unop_fork([unop, P], [binop, Q], [unop, R]) ->
    [unop, [fork, P, Q, R]].

binop_fork([binop, P], [binop, Q], [binop, R]) ->
    [binop, [fork, P, Q, R]].

fork_unop([unop, P], [binop, Q], [unop, R], [term, X]) ->
    ['⊦', [[[fork, P, Q, R], X], '⇔', [[P, X], Q, [R, X]]]].

fork_binop([binop, P], [binop, Q], [binop, R], [term, X], [term, Y]) ->
    ['⊦', [[X, [fork, P, Q, R], Y], '⇔', [[X, P, Y], Q, [X, R, Y]]]].

unop_natp() ->
    [unop, natp].

term_0() ->
    [term, '0'].

natp_0() ->
    ['⊦', [natp, '0']].

unop_succ() ->
    [unop, succ].

natp_succ([term, X]) ->
    ['⊦', [[natp, X], '→', [natp, [succ, X]]]].

binop_plus() ->
    [binop, '+'].

add_0() ->
    ['⊦', ['∀', [fork, natp, '→', [fork, ['_', '+', '0'], '=', id]]]].

add_succ() ->
    ['⊦', ['∀', [fork, [natp, '∘', '⊣'], '→', [fork, [natp, '∘', '⊢'], '→', [fork, [fork, '⊣', '+', [succ, '∘', '⊢']], '=', [succ, '∘', '+']]]]]].

nat_ind([unop, P]) ->
    ['⊦', [[P, '0'],
           '→',
           [['∀', [fork, natp, '→', [fork, P, '→', [P, '∘', succ]]]],
            '→',
            ['∀', [fork, natp, '→', P]]]]].


'0+0=0'() ->
    ['⊦', [['0', '+', '0'], '=', '0']].

'prove_0+0=0'() ->
    P1 = add_0(),
    P1 = ['⊦', ['∀', [fork, natp, '→', [fork, ['_', '+', '0'], '=', id]]]],

    P2 = binop_plus(),
    P2 = [binop, '+'],

    P3 = term_0(),
    P3 = [term, '0'],

    P4 = unop_bind_left(P2, P3),
    P4 = [unop, ['_', '+', '0']],

    P5 = binop_eq(),
    P5 = [binop, '='],

    P6 = unop_id(),
    P6 = [unop, id],

    P7 = unop_fork(P4, P5, P6),
    P7 = [unop, [fork, ['_', '+', '0'], '=', id]],

    P8 = unop_natp(),
    P8 = [unop, natp],

    P9 = binop_imply(),
    P9 = [binop, '→'],

    P10 = unop_fork(P8, P9, P7),
    P10 = [unop, [fork, natp, '→', [fork, ['_', '+', '0'], '=', id]]],

    P11 = forall_inst_unop(P10, P3),
    P11 = ['⊦', [['∀', [fork, natp, '→', [fork, ['_', '+', '0'], '=', id]]],
                 '→',
                 [[fork, natp, '→', [fork, ['_', '+', '0'], '=', id]], '0']]],

    P12 = mp(P1, P11),
    P12 = ['⊦', [[fork, natp, '→', [fork, ['_', '+', '0'], '=', id]], '0']],


    P13 = fork_unop(P8, P9, P7, P3),
    P13 = ['⊦', [[[fork, natp, '→', [fork, ['_', '+', '0'], '=', id]], '0'],
                 '⇔',
                 [[natp, '0'], '→', [[fork, ['_', '+', '0'], '=', id], '0']]]],

    P14 = unop(P10, P3),
    P14 = [term, [[fork, natp, '→', [fork, ['_', '+', '0'], '=', id]], '0']],

    P15 = unop(P8, P3),
    P15 = [term, [natp, '0']],

    P16 = unop(P7, P3),
    P16 = [term, [[fork, ['_', '+', '0'], '=', id], '0']],

    P17 = binop(P9, P15, P16),
    P17 = [term, [[natp, '0'], '→', [[fork, ['_', '+', '0'], '=', id], '0']]],

    P18 = iff_left(P14, P17),
    P19 = mp(P13, P18),
    P20 = mp(P12, P19),
    P20 = ['⊦', [[natp, '0'], '→', [[fork, ['_', '+', '0'], '=', id], '0']]],

    P21 = natp_0(),
    P21 = ['⊦', [natp, '0']],
    P22 = mp(P21, P20),
    P22 = ['⊦', [[fork, ['_', '+', '0'], '=', id], '0']],

    P23 = fork_unop(P4, P5, P6, P3),
    P23 =  ['⊦', [[[fork, ['_', '+', '0'], '=', id], '0'],
                  '⇔',
                  [[['_', '+', '0'], '0'], '=', [id, '0']]]],

    P24 = unop(P4, P3),
    P24 = [term, [['_', '+', '0'], '0']],

    P25 = unop(P6, P3),
    P25 = [term, [id, '0']],

    P26 = binop(P5, P24, P25),
    P26 = [term, [[['_', '+', '0'], '0'], '=', [id, '0']]],

    P27 = iff_left(P16, P26),
    P28 = mp(P23, P27),
    P29 = mp(P22, P28),
    P29 = ['⊦', [[['_', '+', '0'], '0'], '=', [id, '0']]],

    P30 = bind_left(P2, P3, P3),
    P30 = ['⊦', [[['_', '+', '0'], '0'], '=', ['0', '+', '0']]],

    P31 = id(P3),
    P31 = ['⊦', [[id, '0'], '=', '0']],

    P32 = binop(P2, P3, P3),
    P32 = [term, ['0', '+', '0']],

    P33 = eq_comm(P24, P32),
    P34 = mp(P30, P33),
    P34 = ['⊦', [['0', '+', '0'], '=', [['_', '+', '0'], '0']]],

    P35 = eq_trans(P32, P24, P25),
    P36 = mp(P34, P35),
    P37 = mp(P29, P36),
    P37 = ['⊦', [['0', '+', '0'], '=', [id, '0']]],

    P38 = eq_trans(P32, P25, P3),
    P39 = mp(P37, P38),
    P40 = mp(P31, P39),
    P40 = ['⊦', [['0', '+', '0'], '=', '0']],
    P40.
