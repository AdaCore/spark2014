procedure Test_Move with SPARK_Mode is
   type T is access Boolean;

   Ptr : constant T := new Boolean'(False);
   function Create return T is
   begin
      return Ptr;
   end;
   function Create_2 return T is
      C : T := Ptr;
   begin
      return C;
   end;
   function Create_3 return T is
      C : T := Ptr;
   begin
      return null;
   end;
   function Create4 return T is
   begin
      return R : T do
         R := Ptr;
      end return;
   end;
   function Create_5 return T is
      C : T := Ptr;
   begin
      return R : T do
         R := C;
      end return;
   end;
begin
   null;
end Test_Move;
