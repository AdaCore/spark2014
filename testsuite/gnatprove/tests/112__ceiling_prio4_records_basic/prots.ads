package Prots is

   protected type PT1 with Priority => 3 is
      procedure PP1
      with Global => null, Always_Terminates;
   end;

   protected type PT2 with Priority => 4 is
      procedure PP2
      with Global => null, Always_Terminates;
   end;

   type R is record
      F1 : PT1; --  Inherited priority 3
      F2 : PT2; --  Inherited priority 4
      F3 : PT1; --  Inherited priority 3
      -- F3 has intentionally the same type as F1. Just to have multiple
      -- instances of one type. Note that in SPARK it is not possible to to
      -- have different priorities for the fields of one and the same component
      -- type. Whereas components having different types can also have
      -- different (inherited) priorities.
   end record;

   protected PO
     with Priority => 3
   is
      procedure PP0
      with Global => null, Always_Terminates;
   end;

   procedure Proc1;
   --  Priority of the caller must be <= 3
   procedure Proc2;
   --  Priority of the caller must be <= 3

end Prots;
