%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ASP-Encoding for initial sets
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% List of predicates
%
% arg/1       arguments of AF
% att/2       attack-relation
% attacked/1  attacked argument
% card/1      cardinality of solution candidate
% excl/2      argument excluded from set
% in/1	      argument of solution candidate
% lt/2        lower-than relation over arguments of solution candidate
% ninf/1      non-smallest arguments of solution candidate
% non_def/3   non-defended argument of subset of solution candidate
% non_empty   indicates non-emptyness of solution candidate
% non_adm/2   indicates non-admissibility of subset
% nsucc/2     non-successor relation over arguments of solution candidate
% sub/2       argument of decremented set
% sub/3       argument of descending subsets
% sub_attacked/3 argument attacked by subset
% succ/2      successor-relation over arguments of solution candidate

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

#show in/1.
