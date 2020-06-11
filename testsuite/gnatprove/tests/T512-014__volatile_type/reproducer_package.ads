package Reproducer_Package
is
	type Random_Type  is mod 2 ** 64;
	type Async_Reader_Type is record
		Component : Random_Type;
	end record
	with
		Volatile,
		Async_Readers;
		
	type Test_Type is limited record
		Async_Reader_Component : Async_Reader_Type;
	end record
	with
		Volatile,
		Async_Readers,
		Predicate => Async_Reader_Component.Component < 5;
	
end Reproducer_Package;
