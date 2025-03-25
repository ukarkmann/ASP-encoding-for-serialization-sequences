%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ASP-Encoding for unchallenged initial sets
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Algorithm
%
% 0.	Generate sets of arguments as solution candidates
%
% 1. 	Exclude non-initial solution candidates 
%
%		1.1	Exclude empty set
%		1.2	Exclude conflicting sets
%		1.3	Exclude non-admissible sets
%			=> Remaining sets are non-empty admissible
%		1.4	Exclude non-minimal admissible sets
%			
%			1.4.1	Define subsets decremented by one element
%			1.4.2	Define subsubsets by removing all non-defended arguments
%			1.4.3	Flag non-admissible subsets
%			=> Non-flagged subsets are admissible
%			1.4.4 	Exclude solution candidate with admissible subset
%
%		=> Remaining sets are initial sets
%
%		1.5	Exclude unattacked sets 
%
% 2.	Exclude solution candidates not attacked by initial set
%
%	2.1	Define arguments outside solution candidate
%	2.2 	Define all non-empty subsets of 'out'
%	2.3	Flag non-initial subsets of 'out'
%		2.3.1	Flag conflicting subsets
% 		2.3.2	Flag non-admissible subsets 
% 		2.3.3	Flag non-minimal subsets
% 		=> Non-flagged subsets are initial sets in out
%	2.4	Exclude solution candidates not attacked by initial sets
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% List of used predicates
%
% arg/1       arguments of AF
% att/2       attack-relation
% attacked/1  attacked argument
% card/1      cardinality of solution candidate
% elemIni     element of out-initial set
% excl/2      argument excluded from solution candidate
% in/1	      argument of solution candidate
% in_attacked attacked solution candidate
% ini_attack  solution candidate attacked by initial set
% iniSet/1    initial set not in solution candidate
% lt/2        lower-than relation over arguments of solution candidate
% ninf/1      non-smallest arguments of solution candidate
% nonAdm/1    indicates non-admissibility of subset
% non_empty   non-empty solution candidate
% nsucc/2     non-successor relation over arguments of solution candidate
% o_attacked/1 attacked argument not in solution candidate
% o_card/1    cardinality of arguments not in solution candidate 
% o_elem/2    element of subset of arguments not in solution candidate
% o_flag/1    flag non-initials subsets not in solution candidate
% o_lt/2      lower-than relation over arguments not in solution candidate
% o_nsucc/2   non-successor relation over arguments not in solution candidate
% o_ninf/1    non-smallest arguments not in solution candidate
% o_set/1     number of subset of 'out'
% o_sub/2     subsets of subsets not in solution candidate
% o_vec/4     binary vector
% out/1	      argument not in solution candidate
% out/2       numbered argument not in solution candidate
% sub/2       argument of decremented solution candidate
% sub_attacked/2 argument attacked by subset
% succ/2      successor-relation over arguments of set

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% 	0.	Generate sets of arguments as candidates for initial set

	{ in(X) } 		:- 	arg(X).

%	1.1	Exclude empty set

	non_empty 		:- 	in(X).
					
				:- 	not non_empty.

%	1.2	Exclude conflicting sets

				:- 	in(X), 
					in(Y), 
					att(X, Y).

%	1.3	Exclude non-admissible sets

% 	Select arguments attacked by 'in'

	attacked(X) 		:- 	in(Y), 
					att(Y, X).

% 	Exclude sets with non-defended arguments

				:- 	att(Y, X), 
					in(X), 
					not attacked(Y).

%	RESULT: Remaining sets are non-empty admissible

%	1.4	Exclude non-minimal admissible sets

%	Define an order on each set with succ-relation

	lt(X, Y) 		:- 	in(X),
					in(Y), 
					X<Y.
					
	nsucc(X, Z) 		:- 	lt(X, Y), 
					lt(Y, Z).
					
	succ(X, Y) 		:- 	lt(X, Y), 
					not nsucc(X, Y).
					
	ninf(X) 		:- 	lt(Y, X).

% 	Define numbered arguments to be excluded

	excl(X, 1) 		:- 	not ninf(X), 
					in(X).
					
	excl(Y, No+1) 		:- 	excl(X, No), 
					in(Y), 
					succ(X, Y).

%	1.4.1	Define subsets decremented by one element

	sub(X, No)		:- 	in(X),
					not excl(X, No),
					card(C),
					No = 1..C.

%	Define first 'level' of subsets

	sub(X, No, 0)		:-	sub(X,No).
	
% 	Select arguments attacked by 'sub'

	sub_attacked(Y, No, Level):-	sub(X, No, Level),
					att(X, Y).
					
%	Select non-defendet arguments of 'sub'

	non_def(Y, No, Level)	:-	sub(Y, No, Level),
					att(X, Y),
					not sub_attacked(X, No, Level).

%	1.4.2	Define subsubsets by removing non-defended arguments

	card(C)			:- 	{ in(X) } == C.

	sub(X, No, Level+1)	:-	sub(X, No, Level),
					not non_def(X, No, Level),
					card(C),
					Level < C. 

%	1.4.3 	Flag non-admissible subsets

	non_adm(No, Level)	:-	non_def(Y, No, Level).


%	1.4.4	Exclude solution candidate with admissible subset
	
				:-	not non_adm(No, Level),
					sub(X, No, Level).

%	1.5	Exclude unattacked sets

	in_attacked		:- 	in(X),
					att(Y,X),
					arg(Y).

				:-	not in_attacked.

%	2. 	Exclude sets attacked by initial sets

%	2.1	Define arguments outside solution candidate

	out(X) 			:- 	arg(X), 
					not in(X).

%	2.2 	Define all non-empty subsets of 'out' (including identity)

%	Define an order over 'out' with succ-relation

	o_lt(X,Y) 		:- 	out(X),
					out(Y), X<Y.
					
	o_nsucc(X,Z) 		:- 	o_lt(X,Y), 
					o_lt(Y,Z).
					
	o_succ(X,Y) 		:- 	o_lt(X,Y), 
					not o_nsucc(X,Y).
					
	o_ninf(X) 		:- 	o_lt(Y,X).

% 	Each out-argument is numbered accordingly

	out(X, 0) 		:- 	not o_ninf(X), 
					out(X).
					
	out(Y, ArgNo+1) 	:- 	out(X, ArgNo), 
					out(Y), 
					o_succ(X, Y).

%	Define numbered subsets and use binary vector of subset-number
%	to assign in-arguments to the corresponding subset

% 	Number of subsets equals cardinality of power-set
% 	= 2^ (cardinality of set), "0" corresponds to empty set,
% 	maximum corresponds to identity
	
	o_card(C) 		:- 	{ out(X) } == C.
	
	o_set(1..SetNo) 	:- 	(2 ** C) - 1 == SetNo, 
					o_card(C).

% 	Calculate binary vector by repeatedly divide number by 2.
% 	Rest is 1 or 0 and assigns argument to subset
% 	Result is needed for the next division

%	Start

	o_vec(SetNo, 0, SetNo\2, SetNo/2) :-
					o_set(SetNo).

%	Next

	o_vec(SetNo, ArgNo+1, Result\2, Result/2) :-
					o_vec(SetNo, ArgNo, _, Result),
					SetNo >= (2 ** (ArgNo+1)).

% 	Define elements of out-subset
	
	o_elem(SetNo, ArgNo)	:-	o_vec(SetNo, ArgNo, Rest, _),
					Rest = 1.

% 	Define subsets of out-subset (w/o empty set and identity)

	o_sub(SetNo, SubSet) 	:-	o_vec(SetNo, ArgNo, Rest, Result),
					Rest = 1,
					SubSet = 2 ** (ArgNo).

	o_sub(SetNo, SubA+SubB)	:-	o_sub(SetNo, SubA),
					o_sub(SetNo, SubB),
					SubA != SubB,
					SubA + SubB < SetNo.

%	2.3	Flag non-initial subsets of 'out'

% 	2.3.1	Flag conflicting subsets

	o_flag(SetNo) 		:- 	o_elem(SetNo, ArgNo1), 
					o_elem(SetNo, ArgNo2), 
					out(X, ArgNo2), 
					out(Y, ArgNo1), 
					att(X, Y).

% 	2.3.2	Flag non-admissible subsets 
	
	o_attacked(SetNo, X) 	:- 	o_elem(SetNo, ArgNo), 
					out(Y, ArgNo), 
					att(Y, X).
					
	o_flag(SetNo)		:- 	o_elem(SetNo, ArgNo),
					out(X, ArgNo), 
					att(Y,X), 
					not o_attacked(SetNo, Y).
					
% 	2.3.3	Flag non-minimal subsets
	
	o_flag(SetNo1) 		:- 	o_set(SetNo1), 
					o_set(SetNo2), 
					SetNo1 != SetNo2, 
					o_sub(SetNo1, SetNo2),
					not o_flag(SetNo2).
					
% 	RESULT:	Non-flagged subsets are initial sets in out

%	2.4	Exclude solution candidates not attacked by initial sets

	iniSet(SetNo)		:- 	o_set(SetNo), 
					not o_flag(SetNo).
					
	elemIni(SetNo, X)	:-	iniSet(SetNo),
					o_elem(SetNo, ArgNo),
					out(X, ArgNo).
					 
	ini_attack		:-	elemIni(SetNo, X),
					in(Y), 
					att(X,Y).
					
				:-	not ini_attack.	

#show in/1.
