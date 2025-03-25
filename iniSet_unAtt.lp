%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ASP-Encoding for unattacked initial sets
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%	Generate sets of arguments as solution candidates 

	{ in(X) }		:- 	arg(X).


%	Exclude solution candidates with cardinality not 1
 
				:- 	{ in(X) } != 1.

%	Exclude solution candidates with attacked arguments

				:- 	in(X), 
					att(Y,X), 
					arg(Y).

#show in/1.
