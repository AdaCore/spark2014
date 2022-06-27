procedure Constant_Access with SPARK_Mode is
   type Int_Acc is access Integer;
   type List;
   type List_Acc is access List;
   type List is record
      D : not null Int_Acc;
      N : List_Acc;
   end record;

   type C_List;
   type C_List_Acc is access constant C_List;
   type C_List is record
      D : Integer;
      N : C_List_Acc;
   end record;

   function Deep_Copy (X : List_Acc) return C_List_Acc with Ghost;

   function Deep_Copy (X : List_Acc) return C_List_Acc is
   begin
      if X = null then
         return null;
      else
         return new C_List'(D => X.D.all, --@RESOURCE_LEAK:FAIL
                            N => Deep_Copy (X.N));
      end if;
   end Deep_Copy;

   type C_List_Acc_2 is access constant List;

   function Deep_Copy_2 (X : List_Acc) return C_List_Acc_2 with Ghost;

   function Deep_Copy_2 (X : List_Acc) return C_List_Acc_2 is
      function Deep_Copy_Ann (X : List_Acc) return List_Acc with
        Annotate => (GNATprove, Always_Return),
        Post => (Deep_Copy_Ann'Result = null) = (X = null)
      is
      begin
         if X = null then
            return null;
         else
            return new List'(D => new Integer'(X.D.all),
                             N => Deep_Copy_Ann (X.N));
         end if;
      end Deep_Copy_Ann;
   begin
      pragma Assert ((Deep_Copy_Ann (X) = null) = (X = null)); --@RESOURCE_LEAK:FAIL
      pragma Assert ((C_List_Acc_2 (Deep_Copy_Ann (X)) = null) = (X = null)); --@RESOURCE_LEAK:FAIL
      return C_List_Acc_2 (Deep_Copy_Ann (X)); --@RESOURCE_LEAK:FAIL
   end Deep_Copy_2;
begin
   null;
end Constant_Access;
