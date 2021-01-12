procedure Main with SPARK_Mode is
   type Int_Ptr is access Integer;
   type Fun_Ptr is access function (X : Int_Ptr) return Integer;

   procedure P (Obj : Int_Ptr; Fun : Fun_Ptr) is
      Y : constant Integer := Fun (Obj);
   begin
      null;
   end;
begin
   null;
end;
