package body Dispatch with SPARK_Mode is

   procedure P (X : in out T1; B : out Boolean) is
   begin
      B := True;
   end;
   function FF (X : T1) return Boolean is (True);
   function F (X : in out T1) return Boolean is
   begin
      return True;
   end;

   procedure P (X : in out T2; B : out Boolean) is
   begin
      B := True;
   end;
   function FF (X : T2) return Boolean is (True);
   function F (X : in out T2) return Boolean is
   begin
      return True;
   end;

end Dispatch;
