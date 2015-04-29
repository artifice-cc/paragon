:- set_prolog_flag(verbose, silent).
:- initialization(main).

:- dynamic(mm_option/1).

main :- current_prolog_flag(argv, Argv),
	[Filename,MM|_] = Argv,
	format('Input file: ~q~n', Filename), nl,
	format('MM option: ~q~n', MM), nl,
	assert(mm_option(MM)),
	@(Filename),
	halt.
			       
:- style_check(-singleton).

t(Filename).

t(Filename) :-
        @(Filename),
        write('Thank you for your attention.').

?- op(1200,fx,@).
?- op(1200,xfx,?-).

@(FileName) :-
        see(FileName),
        repeat,
        read(Term),
        (Term=end_of_file -> (seen, !) ;
         Term = (Steps ?- WhitenedSentences) ->
         contract(Steps,WhitenedSentences,Residue)).

contract(X,A,D) :-
        list_to_ord_set(X,Y),
        list_to_ord_set(A,B),
        writeproblem(Y,B),
        now_contract(Y,B,D),
        print('ANSWER: '), nl,
        printsteps(D), nl,
        write('###################################'), nl,
        % fail.    % Use this line for multiple answers to each problem.
        !. % Use this line for the first answer to each problem.

writeproblem(X,A) :-
        print('What is the result of contracting the system'), nl,
        printsteps(X), nl,
        print('with respect to the set of sentences'), nl,
        print('['),
        printsentences(A),
        print(']'),
        print(' ?'), nl.


now_contract(System,Whitened,Contraction) :-
        contraction(down,System,Whitened,Contraction).

contraction(_,[ ], _,[ ]).
contraction(_,X,[ ],X).
contraction(down,System,Whitened,Contraction) :-
        print('Now I am in Downward mode.'), nl,
        print('Residual system: '), nl,
        printsteps(System), nl,
        print('Whitened sentences: '),
        printsentences(Whitened), nl,
        existentialclosure(System,Whitened,Closure),
        print('Existential closure: '), nl,
        printsteps(Closure),nl,
        subtract(System,Closure,System1),
        print('New Residual system: '), nl,
        printsteps(System1), nl,
	remainingwhite(System1,Whitened,Whitened1),
        print('Remaining reddened sentences: '),
        printsentences(Whitened1), nl,
        ((Whitened1 = [ ], (Contraction = System1,
                            print('Final contraction is: '),
                            printsteps(Contraction), nl
                           % turn on for minimal mutilation contraction:
                           , mmtest_and_report(System1,System,Whitened), nl
                           ));
         (\+(Whitened1 = [ ]),(contraction(up,System1,Whitened1,Contraction),
                               print('Now changing to Upward mode ... '), nl
                              ))).
contraction(up,System,Whitened,Contraction) :-
        print('Now I am in Upward mode.'), nl,
        print('Residual system: '), nl,
        printsteps(System), nl,
        print('Whitened sentences: '),
        printsentences(Whitened), nl,
        all_premise_sets(System,Whitened,Family),
        list_to_ord_set(Family,Family1),
        ord_union(Family1,Union),
        list_to_ord_set(Union,Set),
        extract_cluster(Set,Set,Cluster),
        print('leading me to identify the following cluster of premise-sets: '),
        printsetsofpremises(Cluster), nl,
        occluder(Cluster,Occluder),
        print('for which I choose the following occluder: '),
        printsentences(Occluder), nl,
        print('and then change to Downward mode ...'), nl,
        contraction(down,System,Occluder,Contraction).

mmtest_and_report(System1,System,Whitened) :-
        mm_option(off).

mmtest_and_report(System1,System,Whitened) :-
        mm_option(on),
        mm(System1,System,Whitened),
        !,
        print('This contraction is minimally mutilating.'), nl.
mmtest_and_report(System1,System,Whitened) :-
        !,
        print('This contraction is NOT minimally mutilating.').
mm(R,T,Unwanted) :-
        list_to_ord_set(R,R1),
        list_to_ord_set(T,T1),
        subtract(T1,R1,TminusR),
        fsso(TminusR,X),
        nonempty(X),
        passes1and2(R,X,T,Unwanted),
        fail.
mm(R,T,Unwanted).

%% fsso(X,Y): find a subset of X and call it Y.
%% This will generate every possible subset of X upon backtracking.
fsso([ ],[ ]).
fsso([H|T],[H|Z]) :-
        fsso(T,Z).
fsso([H|T],Y) :-
        fsso(T,Y).
nonempty([ ]) :-
        fail.
nonempty([H|_]) :-
        !.
passes1and2(R,X,T,Unwanted) :-
        union(R,X,S),
        pc(X,S),
        !,
        cdm(T,S),
        !,
        free_of(Unwanted,S),
        !.
passes1and2(R,X,T,Unwanted) :-
        !,
        fail.

%% Note: pc(X,S) means that every premise of a step in X is the conclusion
%% of some step in S. This suffices as a test for S's being a subnetwork of T,
%% since we already know that R is one.
pc([ ],_) :- !.
pc([H|T],[ ]) :- !,
        fail.
pc([H|T],Y) :-
        pc_this_step(H,Y),
        !,
        pc(T,Y),
        !.
pc_this_step([Prem,Con],Y) :-
        pc_this_node(Prem,Y),
        !.
pc_this_node([ ],_) :-
        !.
pc_this_node([H|T],Y) :-
        conc(H,Y),
        !,
        pc_this_node(T,Y),
        !.

%% conc(H,Y): H is the conclusion of some step in Y.
conc(Conclusion,[ ]) :-
        !,
        fail.
conc(Conclusion,[[_,Conclusion]|_]) :-
        !.
conc(Conclusion,[H|T]) :-
        !,
        conc(Conclusion,T).

%% cdm(T,R): R is closed downwards modulo T; that is, for any step [U,X]
%% in T, if every node in U is a conclusion of a step in R, then [U,X] is in R.
cdm([ ],_).
cdm([[U,X]|Tail_of_T],R) :-
        member([U,X],R),
        !,
        cdm(Tail_of_T,R).
cdm([[U,X]|Tail_of_T],R) :-
        black_in(R,U),
        !,
        fail.
cdm([[U,X]|Tail_of_T],R) :-
        !,
        cdm(Tail_of_T,R).

%% green in(R,U): every node in U is the conclusion of some step in R.
black_in(_,[ ]).
black_in(R,[H|T]) :-
        conc(H,R),
        !,
        black_in(R,T).
black_in(R,[H|T]) :-
        !,
        fail.

%% free of(U,S): no node in U is the conclusion of any step in S
free_of([ ],_).
free_of([H|T],S) :-
        conc(H,S),
        !,
        fail.
free_of([H|T],S) :-
        !,
        free_of(T,S).


occluder([ ],[ ]).
occluder([CH|CT],Occluder) :-
        member(X,CH),
        setsFrom(CT,thatHave(X,CTHits,andthe(CTMisses))),
        ord_intersection([CH|CTHits],Ord_IntersectHits),
        subtract_from_members(CTMisses,Ord_IntersectHits,Pruned_CTMisses),
        occluder(Pruned_CTMisses,Occluder1),
        ord_add_element(Occluder1,X,Occluder).

setsFrom([ ],thatHave(_,[ ],andthe([ ]))).
setsFrom([H|T],thatHave(X,[H|SetOfTailHits],andthe(SetOfTailMisses))) :-
        member(X,H),
        !,
        setsFrom(T,thatHave(X,SetOfTailHits,andthe(SetOfTailMisses))).
setsFrom([H|T],thatHave(X,SetOfTailHits,andthe([H|SetOfTailMisses]))) :-
        setsFrom(T,thatHave(X,SetOfTailHits,andthe(SetOfTailMisses))).

ord_intersection([H],H).
ord_intersection([H|[K|T]],Ord_Intersect) :-
        ord_intersection([K|T],Ord_IntersectKT),
        ord_intersect(H,Ord_IntersectKT,Ord_Intersect).

occludes(Cluster,Occluder) :-
        !,
        hits(Occluder,Cluster),
        hitsperfectly(Occluder,Cluster).

hitsperfectly(Occluder,Cluster) :-
        member(X,Occluder),
        ord_del_element(Occluder,X,WouldBeOccluder),
        hits(WouldBeOccluder,Cluster),
        !,
        fail.
hitsperfectly(Occluder,Cluster).

remainingwhite(System,[ ],[ ]).
remainingwhite(System,[H|T],[H|U]) :-
        conc(H,System),
        !,
        remainingwhite(System,T,U).
remainingwhite(System,[H|T],U) :-
        !,
        remainingwhite(System,T,U).

existentialclosure(System,Whitened,Closure) :-
        existentialclosure(System,Whitened,Closure,[ ]).
existentialclosure([ ],Whitened,Closure,[ ]) :-
        !,
        solutions([[P],P],member(P,Whitened),Closure).
existentialclosure(_,[ ],Buildup,Buildup) :-
        !.
existentialclosure(System,Whitened,Closure,Buildup) :-
        prem(Whitened,System),
        !,
        infected(Whitened,System,Infected),
        subtract(System,Infected,System1),
        union(Buildup,Infected,Biggerbuildup),
        freshlywhite(Whitened,System1,Infected,Freshlywhitened),
        conclusions(Freshlywhitened,Freshwhitened),
        existentialclosure(System1,Freshwhitened,Closure,Biggerbuildup).
existentialclosure(System,Whitened,Buildup,Buildup) :-
        !.

conclusions([ ],[ ]).
conclusions([[Premises,Conclusion]|T],[Conclusion|Conclusions]) :-
        !,
        conclusions(T,Conclusions).

freshlywhite(Whitened,System,[ ],[ ]).
freshlywhite(Whitened,System,[[Prems,Conclusion]|T],[[Prems,Conclusion]|U]) :-
        \+(member(Conclusion,Whitened)),
        \+(conc(Conclusion,System)),
        !,
        freshlywhite(Whitened,System,T,U).
freshlywhite(Whitened,System,[H|T],U) :-
        !,
        freshlywhite(Whitened,System,T,U).

infected(Whitened,[ ],[ ]).
infected(Whitened,[[Premises,Conclusion]|T],[[Premises,Conclusion]|U]) :-
        list_to_ord_set(Whitened,Whitened1),
        list_to_ord_set(Premises, Premises1),
        ord_intersect(Premises1,Whitened1),
        !,
        infected(Whitened,T,U).
infected(Whitened,[H|T],U) :-
        !,
        infected(Whitened,T,U).

prem([ ], _) :-
        !,
        fail.
prem(_,[ ]) :-
        !,
        fail.
prem(Whitened,[[Premises,Conclusion]|T]) :-
        list_to_ord_set(Whitened,Whitened1),
        list_to_ord_set(Premises, Premises1),
        ord_intersect(Premises1,Whitened1),
        !.
prem(Whitened,[[Premises,Conclusion]|T]) :-
        prem(Whitened,T).

all_premise_sets([ ], _,[ ]).
all_premise_sets(_,[ ],[ ]).
all_premise_sets(System,[H|T],[H1|T1]) :-
        !,
        premise_sets(System,H,H0),
        list_to_ord_set(H0,H1),
        all_premise_sets(System,T,T1).

premise_sets([ ],_,[ ]).
premise_sets([[Prems,Conclusion]|SystemTail],Conclusion,[Prems|T]) :-
        !,
        premise_sets(SystemTail,Conclusion,T).
premise_sets([SystemHead|SystemTail],Conclusion,T) :-
        !,
        premise_sets(SystemTail,Conclusion,T).

extract_cluster(_,[ ],[ ]).
extract_cluster(X,[H|T],U) :-
        iism(X,H),
        ord_del_element(X,H,X0),
        !,
        extract_cluster(X0,T,U).
extract_cluster(X,[H|T],[H|U]) :-
        !,
        extract_cluster(X,T,U).

iism([ ],_) :-
        fail.
iism([X|Y],H) :-
        subset(X,H),
        \+(subset(H,X)),
        !.
iism([X|Y],H) :-
        iism(Y,H).

subtract_from_members([ ], _,[ ]).
subtract_from_members([H|T],Y,[H1|T1]) :-
        subtract(H,Y,H1),
        subtract_from_members(T,Y,T1).

hitter([ ],[ ]).
hitter([CH|CT],Hitter) :-
        member(X,CH),
        setOfMisses(X,CT,CT1),
        hitter(CT1,Hitter1),
        ord_add_element(Hitter1,X,Hitter).

hits(_,[ ]).
hits([ ],_) :-
        !,
        fail.
hits(X,[H|T]) :-
        list_to_ord_set(X,X1),
        list_to_ord_set(H,H1),
        ord_intersect(X1,H1),
        hits(X,T),
        !.

setOfMisses(X,[ ],[ ]).
setOfMisses(X,[H|T],[H|U]) :-
        \+(member(X,H)),
        !,
        setOfMisses(X,T,U).
setOfMisses(X,[H|T],U) :-
        !,
        setOfMisses(X,T,U).

preprocess(X,Y) :-
        dependency_network(X),
        nodes(Y).

dependency_network(X) :-
        !,
        list_of_steps(X),
        pc(X,X).

nodes([ ]).
nodes([H|T]) :-
        node(H),
        nodes(T),
        !.

node(a).
node(b).
node(c).
node(d).
node(e).
node(f).
node(g).
node(h).
node(i).
node(j).

%%. . . etcetera, for as many primitive nodes as one wishes.

list_of_steps([ ]).
list_of_steps([H|T]) :-
        !,
        step(H),
        list_of_steps(T).

step(X) :-
        initial_step(X),
        !.
step(X) :-
        transitional_step(X),
        !.

initial_step([[X],X]) :-
        node(X).

transitional_step([Premisees,Conclusion]) :-
        !,
        node(Conclusion),
        nonempty_list_of_nodes(Premisees),
        list_to_ord_set(Premisees,Premisees1),
        setEq(Premisees,Premisees1),
        \+(member(Conclusion,Premisees)).

nonempty_list_of_nodes([H]) :-
        !,
        node(H).
nonempty_list_of_nodes([H|T]) :-
        !,
        nonempty_list_of_nodes(T).

premise_sets_of([ ],[ ]).
premise_sets_of([[Premises,Conclusion]|T],[Premises|T1]) :-
        premise_sets_of(T,T1),
        !.

ord_union(ListOfSets,Union) :-
        length(ListOfSets,Length),
        ((Length =:= 0, Union = [ ]);
         (\+(Length =:= 0), ord_union(Length,ListOfSets,Union,[ ]))).
ord_union(1,[Set|Sets],Set,Sets) :-
        !.
ord_union(N,Sets0,Union,Sets) :-
        A is N//2,
        ord_union(A,Sets0,X,Sets1),
        Z is N-A,
        ord_union(Z,Sets1,Y,Sets),
        union(X,Y,Union).

allconclusions([ ],_).
allconclusions([H|T],Y) :-
        member([Premises,H],Y),
        !.

conclusion_in(H,[ ]) :-
        !,
        fail.
conclusion_in(H,[[Head|H]|T]) :-
        !.
conclusion_in(H,[Head|T]) :-
        !,
        conclusion_in(H,T).

%% "Bookkeeping on length of problems etc." code left out

printsteps([ ]) :-
        print('[ ]').
printsteps([H]) :-
        !,
        writestep(H).
printsteps([H|T]) :-
        !,
        writestep(H),
        printsteps(T).

printsentences([ ]) :-
        print('[ ]').
printsentences([H]) :-
        !,
        display(H).
printsentences([H|T]) :-
        !,
        display(H),
        print(','),
        printsentences(T).

writestep([X,A]) :-
        !,
        printsentences(X),
        print(' |- '),
        display(A), nl.

printsetsofpremises([ ]).
printsetsofpremises([H]) :-
        print('['),
        printpremises(H),
        print(']'),
        !.
printsetsofpremises([H|T]) :-
        print('['),
        printpremises(H),
        print(']'),
        print(', '),
        printsetsofpremises(T).

printpremises([ ]).
printpremises([H]) :-
        display(H),
        !.
printpremises([H|T]) :-
        display(H),
        print(', '),
        printpremises(T).


%% EXAMPLES

