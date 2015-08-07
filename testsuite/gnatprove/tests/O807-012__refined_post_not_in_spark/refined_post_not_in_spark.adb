package body Refined_Post_Not_In_SPARK
  with Refined_State => (State => X)
is
   X : Natural := 1;

   function Not_In_SPARK return Boolean
     with SPARK_Mode => Off
   is
     X : aliased Boolean := False;
   begin
     return X;
   end;

   procedure Proc (Par  : in     Integer;
                   Par2 :    out Integer)
     with Refined_Global => X,
          Refined_Post   => Not_In_SPARK
   is
   begin
      Par2 := Par + X;
   end Proc;

end;
