with Types; use Types;

procedure Partial_Assign
  with SPARK_Mode
is

   procedure Update (T : in out Table; I, J : Index)
   with
     Relaxed_Initialization => T,
     Pre => I in T'Range and J in T'Range,
     Post =>
       (for all K in T'Range =>
	 (if K in I .. J then T(K)'Initialized
	  else T(K)'Initialized = T'Old(K)'Initialized));

   procedure Update (T : in out Table; I, J : Index) is
   begin
      T (I .. J) := (I .. J => 42);
   end Update;

   Tab : Table (1 .. 20) with Relaxed_Initialization;

begin
   Tab(1) := 1;
   Tab(20) := Tab (1);

   Tab (2 .. 19) := (others => 42);
   Update (Tab, 2, 19);

   pragma Assert (Tab'Initialized);

end Partial_Assign;
