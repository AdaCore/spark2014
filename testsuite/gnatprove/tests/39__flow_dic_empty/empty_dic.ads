package Empty_DIC with SPARK_Mode is

   type Null_Record is private
     with Default_Initial_Condition => True;

   type Empty_Composite is private
     with Default_Initial_Condition => True;

   --  Control: this type really has an uninitialized ordinary component.
   type Uninitialized_Record is private
     with Default_Initial_Condition => True;

private

   type Null_Record is null record;

   type Empty_Component is null record;

   type Empty_Composite is record
      C : Empty_Component;
   end record;

   type Uninitialized_Record is record
      Value : Integer;
   end record;

end Empty_DIC;
