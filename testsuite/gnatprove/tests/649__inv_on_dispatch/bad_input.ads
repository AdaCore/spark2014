package Bad_Input with SPARK_Mode is
   pragma Elaborate_Body;

   type E is private;

   type Root is abstract tagged null record;

   procedure P (R : Root; X : E; Target : out Integer) is abstract
     with Post'Class => Target >= 0;

   type GrandChild is new Root with private;

   overriding procedure P (R : GrandChild; X : E; Target : out Integer);

   procedure Fail_At_Runtime;

private
   type E is new Integer with Type_Invariant => E >= 0, Default_Value => 0;

   type Child is new Root with null record;

   overriding procedure P (R : Child; X : E; Target : out Integer);

   type GrandChild is new Child with null record;
end Bad_Input;
