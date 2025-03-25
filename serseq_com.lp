%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ASP-Encoding for serialization sequence of complete semantics.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Algorithm
%
% 0.	Generate sequences of sets of arguments as solution candidates
%	for serialization sequences.
%
% 1. 	Each sequence terme must be an initial set
%
%	1.1	Exclude sequences with non-initial terms 
%
%		1.1.1	Exclude sequences with 'intermediate' empty term,
%		1.1.2	Exclude sequences with conflicting term
%		1.1.3	Exclude sequences with non-admissible term
%			=> Remaining sequences only have non-empty admissible
%			   terms
%		1.1.4	Exclude sequences with non-minimal admissible terms
%			
%			1.1.4.1	Create subsets decremented by one element
%			1.1.4.2	Define subsubsets by removing non-defended arguments
%			1.1.4.3 Flag non-admissible subsets
%			=> Non-flagged subsets are admissible
%			1.1.4.4 Exclude sequences with admissible subset
%
%		=> Remaining sequence terms are initial sets
%
% 2.	Termination condition: no unattacked arguments in reduct
%
%	2.1	Flag attacked arguments
%	2.2	Indicate reducts containing unattacked arguments
%	2.3	Exclude sequences with improper last reduct
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% List of predicates
%
% arg/1       arguments of AF
% att/2       attack-relation
% att/3       attack-relation within reduct
% attacked/2  argument attacked by sequence term
% collect/2   argument outside reduct
% excl/3      argument excluded from term
% flag/2      attacked arguments of reduct 
% in/2        argument of sequence term
% index/1     index of sequence term
% in_card/2   cardinality of sequence term
% in_index/2  index of arguments of sequence term
% lt/3        lower-than relation over arguments of sequence term
% ninf/2      non-smallest arguments of sequence term
% non_adm/3   non-admissibility of numbered subset of sequence term
% non_def/4   non-defended arguments of subset of sequence term
% non_empty/1 non-empty sequence term
% non_terminate/1 reduct with unattacked arguments
% nsucc/3     non-successor relation over arguments of sequence term
% reduct/2    argument of reduct
% reduct/3    numbered argument of reduct 
% sub/3       argument of decremented term
% sub/4       argument of subset of sequence term
% sub_attacked/4 argument attacked by subset of sequence term
% succ/3      successor-relation over arguments of sequence term

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%	Get number of arguments

	index(1..C) 		:- 	{ arg(X) } == C.

%	0.	GENERATE sequences of sets of arguments as solution candidates
%		for serialization sequences

	{ in(X, Step) } 	:- 	reduct(X, Step).

%	Get cardinality of sequence terms

	in_index(1..C, Step)	:-	{ in(X, Step) } == C,
					index(Step).

	in_card(C, Step)	:-	{ in(X, Step) } == C,
					index(Step). 

%	Define reduct

%	First reduct equals AF

	reduct(X, 1) 		:- 	arg(X).


%	Collect arguments from sequence term

	collect(X, Step) 	:- 	in(X, Step).

%	Collect arguments attacked by sequence term

	collect(X, Step) 	:- 	in(Y, Step), 
					att(Y, X).

%	Next reduct has all non-collected arguments 

	reduct(X, Step+1) 	:- 	reduct(X, Step), 
					not collect(X, Step), 
					index(Step).

%	.. and the relations between contained arguments

	att(X, Y, Step) 	:- 	reduct(X, Step), 
					reduct(Y, Step), 
					att(X, Y).

% 	1. 	Each sequence term must be an initial set
%
% 	1.1	Exclude sequences with non-initial term
%
% 	1.1.1	Exclude sequences with 'intermediate' empty term

	non_empty(Step)		:- 	in(X, Step).
	
				:-	not non_empty(Step),
					non_empty(Step+1),
					index(Step). 

% 	1.1.2	Exclude sequences with conflicting terms

				:- 	in(X, Step), 
					in(Y, Step), 
					att(X, Y, Step).


% 	1.1.3	Exclude sequences with non-admissible term

% 	Select arguments attacked by element

	attacked(X,Step) 	:- 	in(Y, Step), 
					att(Y, X, Step).

% 	Exclude sequences with non-defended arguments in term

				:- 	att(Y, X, Step), 
					in(X, Step), 
					not attacked(Y, Step).

%	RESULT: Remaining sequences only have non-empty admissible terms

% 	1.1.4	Exclude sequences with non-minimal admissible term
			
% 	1.1.4.1	Create subsets decremented by one element

% 	Define an order over 'in' with succ-relation

	lt(X, Y, Step) 		:- 	in(X, Step),
					in(Y, Step), 
					X<Y.

	nsucc(X, Z, Step) 	:- 	lt(X, Y, Step), 
					lt(Y, Z, Step).

	succ(X, Y, Step) 	:- 	lt(X, Y, Step), 
					not nsucc(X, Y, Step).

	ninf(X, Step) 		:- 	lt(Y, X, Step).

% 	Define numbered arguments to be excluded

	excl(X, 1, Step) 	:- 	not ninf(X, Step), 
					in(X, Step).
					
	excl(Y, No+1, Step) 	:- 	excl(X, No, Step), 
					in(Y, Step), 
					succ(X, Y, Step).

% 	Define decremented sets (w/o excluded argument)

	sub(X, No, Step)	:- 	in(X, Step),
					not excl(X, No, Step),
					in_index(No, Step).

%	Define first 'level' of subsets

	sub(X, No, Step, 0)	:-	sub(X, No, Step).
	
% 	Select arguments attacked by 'sub'

	sub_attacked(Y, No, Step, Level):-
					sub(X, No, Step, Level),
					att(X, Y, Step).
					
%	Select non-defended arguments of 'sub'

	non_def(Y, No, Step, Level):-	sub(Y, No, Step, Level),
					att(X, Y, Step),
					not sub_attacked(X, No, Step, Level).

%	1.1.4.2	Define subsubsets by removing non-defended arguments

	sub(X, No, Step, Level+1):-	sub(X, No, Step, Level),
					not non_def(X, No, Step, Level),
					in_card(C, Step),
					Level < C. 

%	1.1.4.3 Flag non-admissible subsets

	non_adm(No, Step, Level):-	non_def(Y, No, Step, Level).


%	1.1.4.4	Exclude sequences with admissible subset
	
				:-	not non_adm(No, Step, Level),
					sub(X, No, Step, Level).

%	RESULT:	Remaining sequence terms are initial sets

% 	2. 	Termination condition: no unattacked arguments in reduct

%	2.1	Flag attacked arguments

	flag(X, Step) 		:- 	reduct(X, Step), 
					reduct(Y, Step), 
					att(Y, X, Step).
					
%	2.2	Indicate reducts containing unattacked arguments

	non_terminate(Step)	:-	reduct(X, Step),
					not flag(X, Step).

%	2.3	Exclude sequences with improper last reduct

				:-	non_empty(Step),
					not non_empty(Step+1),
					non_terminate(Step+1),
					Step > 0.

%	Exclude improper empty set
					
				:-	not non_empty(1),
					non_terminate(1).
#show in/2.
