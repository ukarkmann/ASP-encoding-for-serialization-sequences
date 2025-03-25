%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ASP-encoding of serialization sequence for unchallenged semantics
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Algorithm
%
% 0.	Generate sequences of sets of arguments as solution candidates
%	for serialization sequences
%
% 1. 	Each sequence term must be an initial set
%
%	1.1	Exclude sequences with 'intermediate' empty term
%	1.2	Exclude sequences with conflicting term
%	1.3	Exclude sequences with non-admissible term
%		=> Remaining sequence terms are non-empty admissible
%	1.4	Exclude sequences with non-minimal admissible term
%			
%		1.4.1	Define subsets decremented by one term
%		1.4.2	Define subsubsets by removing non-defended arguments
%		1.4.3 	Flag non-admissible subsets
%		=> Non-flagged subsets are admissible
%		1.4.4 Exclude sequences with admissible subset
%
%	=> Remaining sequence terms are initial sets
%
% 2.	Exclude sequences with challenged term (attacked by initial set)
%
%	2.1	Define all non-empty subsets of reduct
%	2.2	Flag non-initial subsets
%		2.3.1	Flag conflicting subsets
%		2.3.2	Flag non-admissible subsets
%		2.3.3	Flag non-minimal subsets
%		=> Non-flagged subsets are initial sets
%	2.4	Exclude sequences with terms attacked by non-flagged 
%		subsets
%	
%	=> Remaining sequence terms are unattacked or unchallenged initial sets
%
% 3.	Termination condition: no unattacked or unchallenged initial set in reduct
%
%	3.1	Sign flagged subsets (unsigned subsets are initial sets)
%	3.2	Sign all subsets attacked by non-signed subsets
%		=> Non-signed subsets are unattacked or unchallenged initial sets
%	3.3	Indicate reducts containing non-signed subsets	
%	3.4	Exclude sequences with improper last reduct

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% List of used predicates
%
% arg/1       arguments of AF
% att/2       attack-relation
% att/3       attack-relation within reduct
% attacked/2  argument attacked by sequence term
% attacked/3  argument attacked by subset of sequence term
% binVec/4    binary vector
% card/1      cardinality of set of all arguments
% card/2      cardinality of sequence term
% collect/2   argument outside reduct
% elem/2      relation of subsets and contained arguments
% elem/3      relation of subsets of sequence terms and contained arguments
% elemIni/3   argument of initial set
% excl/3      argument excluded from set
% flag/2      flagged subsets of reduct
% in/2        argument of sequence term
% in/3        numbered argument of sequence term 
% index/1.    index of sequence term
% iniSet/2    initial set
% in_card/2   cardinality of sequence term
% in_index/2  index of elements of sequence term
% lt/3        lower-than relation over arguments of sequence term
% ninf/2      non-smallest arguments of sequence term
% non_adm/2   indicates non-admissiblity of subset of sequence term
% non_def/4   mom-defended arguments of subset
% non_empty/1 non-emptiness of sequence term
% non_terminate/1 indicates non-terminating reducts
% nsucc/3     non-successor relation over arguments of sequence term
% r_attacked/3 argument attacked by subset of reduct
% r_card/2    cardinality of reduct 
% r_elem/3    relation of reduct-subset and contained arguments
% r_lt/3      lower-than relation over arguments of reduct
% r_ninf/2    non-smallest arguments of reduct 
% r_nonIS/2   non-initial sets of reduct
% r_nsucc/3   non-successor relation over arguments of reduct
% r_set/2     numbered subset of reduct
% r_sign/2    non-initial set in reduct
% r_sub/3     relation of reduct-subsets and contained subsubsets    
% r_succ/3    successor-relation over arguments of reduct
% reduct/2    argument of reduct
% reduct/3    numbered argument of reduct 
% set/2       numbered subset of sequence term
% sub/2       relation of subsets to contained subsets
% sub/3       argument of decremented set
% sub/4       argument of subsubset
% sub_attacked/2 argument attacked by subset of sequence term
% succ/3      successor-relation over arguments of sequence term
% terminate/1 indicates termination condition

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% 	Get number of arguments

	index(1..C) 		:- 	{ arg(X) } == C.
	card(C) 		:- 	{ arg(X) } == C.


% 	0.	Generate sequences of sets of arguments as solution candidates
%		for serialization sequences

	{ in(X, Step) }	 	:- 	reduct(X, Step).

%	Get cardinality of sequence terms

	in_index(1..C, Step)	:-	{ in(X, Step) } == C,
					index(Step).

	in_card(C, Step)	:-	{ in(X, Step) } == C,
					index(Step). 

%	Define reduct

%	First reduct equals AF

	reduct(X,1) 		:- 	arg(X).

%	Collect arguments from sequence term

	collect(X, Step) 	:- 	in(X, Step).

%	Collect arguments attacked by sequence term

	collect(X, Step) 	:- 	in(Y, Step), 
					att(Y, X).

%	Next reduct has all non-collected arguments 

	reduct(X, Step+1) 	:- 	reduct(X, Step), 
					not collect(X, Step), 
					index(Step).

%	 .. and the relations between contained arguments

	att(X, Y, Step) 	:- 	reduct(X, Step), 
					reduct(Y, Step), 
					att(X, Y).

% 	1. 	Each sequence term must be an initial set

%	1.1	Exclude sequences with non-initial term 

%	1.1.1	Exclude sequences with 'intermediate' empty term

	non_empty(Step)		:- 	in(X, Step).
	
				:-	not non_empty(Step),
					non_empty(Step+1),
					index(Step). 

% 	1.1.2	Exclude sequences with conflicting term

				:- 	in(X, Step), 
					in(Y, Step), 
					att(X, Y).


%	1.1.3	Exclude sequences with non-admissible term

% 	Select arguments attacked by term

	attacked(X, Step) 	:- 	in(Y, Step), 
					att(Y, X, Step).

% 	Exclude sequences with non-defended arguments in term

				:- 	att(Y, X, Step), 
					in(X, Step), 
					not attacked(Y, Step).

%	RESULT: Remaining sequences only have non-empty admissible terms
%			
%	1.1.4	Exclude sequences with non-minimal admissible term

%	1.1.4.1	Create subsets decremented by one term

%	Define an order over 'in' with succ-relation

	lt(X, Y, Step) 		:- 	in(X, Step),
					in(Y, Step), 
					X<Y.

	nsucc(X, Z, Step) 	:- 	lt(X, Y, Step), 
					lt(Y, Z, Step).

	succ(X, Y, Step)	:- 	lt(X, Y, Step), 
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

%	1.1.4.2	Define subsubsets by removing all non-defended arguments

	sub(X, No, Step, Level+1):-	sub(X, No, Step, Level),
					not non_def(X, No, Step, Level),
					in_card(C, Step),
					Level < C. 

%	1.1.4.3 Flag all non-admissible subsets

	non_adm(No, Step, Level):-	non_def(Y, No, Step, Level).


%	1.1.4.4	Exclude sequences with admissible subset
	
				:-	not non_adm(No, Step, Level),
					sub(X, No, Step, Level).
					
%	RESULT: Remaining sequence terms are initial sets

% 2.	Exclude sequences with challenged term (attacked by initial set)

%	2.1	Define all non-empty subsets of reduct

% 	Define an order over reduct with succ-relation

	r_lt(X, Y, Step)	:- 	reduct(X, Step),
					reduct(Y, Step),
					X<Y.
					
	r_nsucc(X, Z, Step)	:- 	r_lt(X, Y, Step), 
					r_lt(Y, Z, Step).
					
	r_succ(X, Y, Step) 	:- 	r_lt(X, Y, Step), 
					not r_nsucc(X, Y, Step).
					
	r_ninf(X, Step) 	:- 	r_lt(Y, X, Step).

% 	Each argument of reduct is numbered accordingly

	reduct(X, Step, 0) 	:- 	not r_ninf(X, Step), 
					reduct(X, Step).
					
	reduct(Y, Step, ArgNo+1):- 	reduct(X, Step, ArgNo), 
					reduct(Y, Step), 
					r_succ(X, Y, Step).

% 	Calculate binary vector by repeatedly divide number by 2.
%	'Rest' is 1 or 0 and assigns argument to subset.
% 	'Result' is needed for the next division

%	Start
	
	binVec(SetNo, 0, SetNo\2, SetNo/2) :-
					card(C),
					(2 ** C) - 1 = Max,
					SetNo = 1..Max.

%	Next

	binVec(SetNo, ArgNo+1, Result\2, Result/2) :-
					binVec(SetNo, ArgNo, _, Result),
					SetNo >= (2 ** (ArgNo+1)).
	
% 	Relate subsets to contained arguments
	
	elem(SetNo, ArgNo) 	:-	binVec(SetNo, ArgNo, Rest, _),
					Rest = 1.
 
% 	Relate subsets to contained subsets (w/o empty set)

	sub(SetNo, SubSet)	:-	binVec(SetNo, ArgNo, Rest, Result),
					Rest = 1,
					SubSet = 2 ** (ArgNo).

	sub(SetNo, SubA+SubB) 	:-	sub(SetNo, SubA),
					sub(SetNo, SubB),
					SubA != SubB,
					SubA + SubB <= SetNo.

% 	Use binary vector to relate reduct-arguments and subsubsets to the 
%	corresponding subset
	
	r_card(C, Step) 	:- 	{ reduct(X, Step) } = C,
					index(Step).
	
	r_set(1..MaxSet, Step) 	:- 	(2 ** C) - 1 == MaxSet, 
					r_card(C, Step).

% 	Relate subsets of reduct to contained arguments for each step
	
	r_elem(SetNo, ArgNo, Step):-	r_set(SetNo, Step),
					elem(SetNo, ArgNo).

% 	Relate subsets of reduct to contained subsets for each step

	r_sub(SetNo, SubSet, Step):-	r_set(SetNo, Step),
					sub(SetNo, SubSet).

%	2.2	Flag non-initial subsets
%	2.3.1	Flag conflicting subsets

	flag(SetNo, Step)	:- 	r_elem(SetNo, ArgNo1, Step), 
					r_elem(SetNo, ArgNo2, Step), 
					reduct(X, Step, ArgNo2), 
					reduct(Y, Step, ArgNo1), 
					att(X, Y, Step).

%	2.3.2	Flag non-admissible subsets
	
	r_attacked(SetNo, X, Step):- 	r_elem(SetNo, ArgNo, Step), 
					reduct(Y, Step, ArgNo), 
					att(Y, X, Step).
					
	flag(SetNo, Step)	:- 	r_elem(SetNo, ArgNo, Step),
					reduct(X, Step, ArgNo), 
					att(Y, X, Step), 
					not r_attacked(SetNo, Y, Step).

%	2.3.3	Flag non-minimal subsets
					
	flag(SetNo1, Step)	:- 	r_set(SetNo1, Step), 
					r_set(SetNo2, Step), 
					SetNo1 != SetNo2, 
					r_sub(SetNo1, SetNo2, Step),
					not flag(SetNo2, Step).

%	RESULT: Non-flagged subsets are initial sets

%	2.3	Exclude sequences with terms attacked by non-flagged subsets

	iniSet(SetNo, Step)	:- 	r_set(SetNo, Step), 
					not flag(SetNo, Step).
					
	elemIni(SetNo, X, Step):-	iniSet(SetNo, Step),
					r_elem(SetNo, ArgNo, Step),
					reduct(X, Step, ArgNo).
					 
				:-	elemIni(SetNo, X, Step),
					in(Y, Step), 
					att(X,Y, Step).
	
%	RESULT: Remaining sequence terms are unattacked or unchallenged initial sets

% 	3. 	Termination condition: no unattacked or unchallenged initial set in reduct
%
%	3.1	Sign flagged subsets (unsigned subsets are initial sets)

	r_sign(SetNo, Step)	:-	flag(SetNo, Step).

%	3.2	Sign all subsets attacked by non-flagged subsets

	r_sign(SetNo1, Step)	:-	r_elem(SetNo1, ArgNo1, Step),
					reduct(X, Step, ArgNo1),
					att(Y, X, Step),
					reduct(Y, Step, ArgNo2),
					r_elem(SetNo2, ArgNo2, Step),
					not flag(SetNo2, Step).

%	RESULT: Non-signed subsets are unattacked or unchallenged initial sets

%	3.4	Indicate reducts containing non-signed subsets	

	non_terminate(Step)	:-	r_set(SetNo, Step),
					not r_sign(SetNo, Step).

%	3.5	Exclude sequences with improper last reduct

				:-	non_empty(Step),
					not non_empty(Step+1),
					non_terminate(Step+1),
					Step > 0.	

%	Exclude improper empty set

				:-	not non_empty(1),
					non_terminate(1).
#show in/2.
