%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ASP-Encoding for unchallenged initial sets
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Algorithm
%
% 0.	Generate sets of arguments as solution candidates
%
% 1. 	Each solution must be an initial set 
%
%	1.1	Exclude empty set
%	1.2	Exclude conflicting sets
%	1.3	Exclude non-admissible sets
%		=> Remaining sets are non-empty admissible
%	1.4	Exclude non-minimal admissible sets
%			
%		1.4.1	Define subsets decremented by one element
%		1.4.2	Define subsubsets by removing non-defended arguments
%		1.4.3	Flag non-admissible subsets
%		=> Non-flagged subsets are admissible
%		1.4.4 	Exclude solution candidate with admissible subset
%
%	=> Remaining sets are initial sets
%
% 2.	Exclude unattacked sets 
%
%	=> Remaining sets are attacked initial sets
%
% 3.	Exclude solution candidates attacked by initial sets
%
%	3.1	Define all non-empty subsets of arguments
%	3.2	Flag non-initial subsets
%		3.2.1	Flag conflicting subsets
% 		3.2.2	Flag non-admissible subsets 
% 		3.2.3	Flag non-minimal subsets
% 		=> Non-flagged subsets are initial sets
%	3.3	Exclude solution candidates attacked by initial set
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% List of used predicates
%
% a_attacked/1 attacked argument
% a_card/1    cardinality of set of arguments 
% a_elem/2    element of subset of arguments
% a_flag/1    flag non-initials subsets
% a_lt/2      lower-than relation over arguments
% a_nsucc/2   non-successor relation over arguments
% a_ninf/1    non-smallest arguments
% a_set/1     number of subset
% a_sub/2     subsets of arguments
% a_vec/4     binary vector
% arg/1       arguments of AF
% arg/2	      numbered argument of AF
% att/2       attack-relation
% attacked/1  attacked argument of solution candidate
% card/1      cardinality of solution candidate
% elemIni     element of initial set
% excl/2      argument excluded from solution candidate
% in/1	      argument of solution candidate
% in_attacked attacked solution candidate
% iniSet/1    initial set
% lt/2        lower-than relation over arguments of solution candidate
% ninf/1      non-smallest arguments of solution candidate
% nonAdm/1    indicates non-admissibility of subset
% non_empty   non-empty solution candidate
% nsucc/2     non-successor relation over arguments of solution candidate
% sub/2       argument of decremented solution candidate
% sub_attacked/2 argument attacked by subset
% succ/2      successor-relation over arguments of set

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% 	0.	Generate sets of arguments as candidates for initial set

	{ in(X) } 		:- 	arg(X).

% 	1. 	Each solution must be an initial set 
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

%	RESULT: Remaining sets are initial sets

%	2.	Exclude unattacked sets

	in_attacked		:- 	in(X),
					att(Y,X),
					arg(Y).

				:-	not in_attacked.
				
%	RESULT: Remaining sets are attacked initial sets				

%	3. 	Exclude solution candidates attacked by initial sets

%	3.1 	Define all non-empty subsets

%	Define an order over all arguments with succ-relation

	a_lt(X,Y) 		:- 	arg(X),
					arg(Y), X<Y.
					
	a_nsucc(X,Z) 		:- 	a_lt(X,Y), 
					a_lt(Y,Z).
					
	a_succ(X,Y) 		:- 	a_lt(X,Y), 
					not a_nsucc(X,Y).
					
	a_ninf(X) 		:- 	a_lt(Y,X).

% 	Each argument is numbered accordingly

	arg(X, 0) 		:- 	not a_ninf(X), 
					arg(X).
					
	arg(Y, ArgNo+1) 	:- 	arg(X, ArgNo), 
					arg(Y), 
					a_succ(X, Y).

%	Define numbered subsets and use binary vector of subset-number
%	to assign arguments to the corresponding subset

% 	Number of subsets equals cardinality of power-set
% 	= 2^ (cardinality of set), "0" corresponds to empty set,
% 	maximum corresponds to identity
	
	a_card(C) 		:- 	{ arg(X) } == C.
	
	a_set(1..SetNo)	 	:- 	(2 ** C) - 1 == SetNo, 
					a_card(C).

% 	Calculate binary vector by repeatedly divide number by 2.
% 	Rest is 1 or 0 and assigns argument to subset
% 	Result is needed for the next division

%	Start

	a_vec(SetNo, 0, SetNo\2, SetNo/2) :-
					a_set(SetNo).

%	Next

	a_vec(SetNo, ArgNo+1, Result\2, Result/2) :-
					a_vec(SetNo, ArgNo, _, Result),
					SetNo >= (2 ** (ArgNo+1)).

% 	Define elements of subsets
	
	a_elem(SetNo, ArgNo)	:-	a_vec(SetNo, ArgNo, Rest, _),
					Rest = 1.

% 	Define subsets of out-subset (w/o empty set and identity)

	a_sub(SetNo, SubSet) 	:-	a_vec(SetNo, ArgNo, Rest, Result),
					Rest = 1,
					SubSet = 2 ** (ArgNo).

	a_sub(SetNo, SubA+SubB)	:-	a_sub(SetNo, SubA),
					a_sub(SetNo, SubB),
					SubA != SubB,
					SubA + SubB < SetNo.
	
%	3.2	Flag non-initial subsets

%	3.2.1	Flag conflicting subsets

	a_flag(SetNo) 		:- 	a_elem(SetNo, ArgNo1), 
					a_elem(SetNo, ArgNo2), 
					arg(X, ArgNo2), 
					arg(Y, ArgNo1), 
					att(X, Y).

% 	3.2.2	Flag non-admissible subsets 
	
	a_attacked(SetNo, X) 	:- 	a_elem(SetNo, ArgNo), 
					arg(Y, ArgNo), 
					att(Y, X).
					
	a_flag(SetNo)		:- 	a_elem(SetNo, ArgNo),
					arg(X, ArgNo), 
					att(Y,X), 
					not a_attacked(SetNo, Y).
					
% 	3.2.3	Flag non-minimal subsets
	
	a_flag(SetNo1) 		:- 	a_set(SetNo1), 
					a_set(SetNo2), 
					SetNo1 != SetNo2, 
					a_sub(SetNo1, SetNo2),
					not a_flag(SetNo2).
					
% 	RESULT:	Non-flagged subsets are initial sets

%	3.3	Exclude solution candidates attacked by initial set

	iniSet(SetNo)		:- 	a_set(SetNo), 
					not a_flag(SetNo).
					
	elemIni(SetNo, X)	:-	iniSet(SetNo),
					a_elem(SetNo, ArgNo),
					arg(X, ArgNo).
					 
				:-	elemIni(SetNo, X),
					in(Y), 
					att(X,Y).

#show in/1.
