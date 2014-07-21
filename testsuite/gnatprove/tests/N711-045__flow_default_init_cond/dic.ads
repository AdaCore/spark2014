package Dic is
   G : Integer;

   type Pr_Record_T is private
     with Default_Initial_Condition;

   type Pr_Record_T2 is private
     with Default_Initial_Condition => Foo (Pr_Record_T2);

   type Pr_Uninit_T is private
     with Default_Initial_Condition => null;

   type Pr_Liar_T is private
     with Default_Initial_Condition;

   function Foo (Par : Pr_Record_T2) return Boolean;

   procedure Do_Stuff;
private
   type Pr_Record_T is record
      X, Y : Integer := 0;
   end record;

   type Pr_Record_T2 is record
      X, Y : Integer := 0;
   end record;

   type Pr_Uninit_T is record
      X : Integer;
      Y : Integer;
   end record;

   type Pr_Liar_T is record
      X : Integer;
      Y : Integer;
   end record;
end Dic;
