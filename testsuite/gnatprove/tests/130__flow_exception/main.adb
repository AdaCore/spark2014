procedure Main (A, B, C : Integer; Z : out Integer)
  with Depends => (Z => (A, B, C)),
       Post    => (if A > 0 then Z = 1
                   elsif A < 0 then Z = -1
                   else  Z = 0)
is
   type By_Copy_Type is new Integer;

   type By_Reference_Type is limited record
      C : Integer;
   end record;

   type By_Unspecified_Type is record
      C : Integer;
   end record;

   procedure Try
     (B : Integer;
      By_Copy      : out By_Copy_Type;
      By_Reference : out By_Reference_Type;
      Unspecified  : out By_Unspecified_Type)
     with Pre => True,
          Post => True,
          Exceptional_Cases => (Program_Error => B > 0, Constraint_Error => B < 0)
   is
   begin
      if B > 0 then
         raise Program_Error;
      elsif B < 0 then
         raise Constraint_Error;
      else
         Unspecified.C := 0;
      end if;
   end;

   By_C : By_Copy_Type;
   By_R : By_Reference_Type;
   By_U : By_Unspecified_Type;

begin
   pragma Assert (A mod 2 = 0);
   Try (A, By_C, By_R, By_U);
   if By_U.C = 0 then
      Z := By_U.C;
      Z := Z + By_R.C;
   else
      Z := - Integer (By_C);
   end if;
exception
   when Constraint_Error =>
      Z := By_U.C + By_R.C + Integer (By_C);
   when Program_Error =>
      Z := C;
end Main;
