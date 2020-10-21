with A; use A;
package Types
  with Elaborate_Body, Annotate => (GNATprove, Terminating)
is
   function Func return Boolean is (R);

   type T1 is private;
   type T2 is private;
   type T3 is private with Default_Initial_Condition => R and Func;

private
   type T1 is new Integer with Invariant => R;
   type T2 is new Boolean with Predicate => not Boolean (T2) and R;
   type T3 is record
      C : Boolean := True;
   end record;

   TO1 : T1 := 3;
   TO2 : T2 := True;
   TO3 : T3;

   procedure Proc1 (Obj : in out T1);
   procedure Proc2 (Obj : in out T2);
   procedure Proc3 (Obj : in out T3);

end;
