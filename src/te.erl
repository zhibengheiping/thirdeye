-module(te).

-export([verify/2]).

verify(Theorem, Proof) when is_function(Theorem) ->
    {arity, N} = erlang:fun_info(Theorem, arity),
    true = is_function(Proof, N),
    Args = [[term, make_ref()] || _ <- lists:seq(1, N)],
    true = apply(Theorem, Args) =:= apply(Proof, Args).
