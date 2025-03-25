%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ASP-Encoding for serialization sequence of strongly admissible semantics.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Algorithm
%
% 0.	Generate sequences of sets of arguments as solution candidates
%	for serialization sequences.
%
% 1. 	Sequence elements must be unattacked initial sets
%	
%	1.1	Exclude sequences with 'intermediate' empty term
%	1.2	Exclude sequences with more than one argument in term
%	1.3	Exclude sequences with attacked arguments
%		
%		=> Remaining sequence terms are unattacked initial sets

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% List of predicates
%
% arg/1       arguments of AF
% att/2       attack-relation
% att/3       attack-relation within reduct
% collect/2   argument outside reduct
% flag/2      attacked argument of term
% in/2        argument of solution candidate
% index/1     index of sequence term
% non_empty/1 non-empty term
% non_terminate non-terminating reduct
% reduct/2    argument of reduct 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% 	Get number of arguments

	index(1..C) 		:- 	{ arg(X) } == C.

%	0.	GENERATE sequences of sets of arguments as solution candidates
%		for serialization sequences.

	{ in(X, Step) } 	:- 	reduct(X, Step).

%	Define reduct

%	First reduct equals AF

	reduct(X,1) 		:- 	arg(X).


%	Collect arguments from sequence term

	collect(X, Step) 	:- 	in(X,Step).


%	Collect arguments attacked by sequence term

	collect(X, Step) 	:- 	in(Y,Step), 
					att(Y,X).


%	Next reduct has all non-collected arguments 

	reduct(X, Step+1) 	:- 	reduct(X,Step), 
					not collect(X,Step),
					index(Step).

%	 .. and the relations between contained arguments

	att(X, Y, Step) 	:- 	reduct(X, Step), 
					reduct(Y, Step), 
					att(X, Y).

%	1	Sequence terms must be unattacked initial sets

% 	1.1	Exclude sequences with 'intermediate' empty term

	non_empty(Step)		:- 	in(X, Step).
	
				:-	not non_empty(Step),
					non_empty(Step+1),
					index(Step). 

%	1.2	Exclude sequences with more than one argument in term

				:- 	in(X, Step),
					in(Y, Step),
					X != Y.

%	1.3	Exclude sequences with attacked arguments

				:- 	in(X, Step), 
					att(Y, X, Step), 
					reduct(Y, Step).
					
%	RESULT: Remaining sequence terms are unattacked initial sets

#show in/2.
