procedure Test with SPARK_Mode is

   function At_End_1 (X : access constant Integer) return access constant Integer with
     Ghost,
     Import,
     Annotate => (GNATprove, At_End_Borrow);

   function At_End_2 (X : access constant Integer) return access constant Integer with
     Ghost,
     Annotate => (GNATprove, At_End_Borrow);
   function At_End_2 (X : access constant Integer) return access constant Integer
     with SPARK_Mode => Off
   is
   begin
      return X;
   end At_End_2;

begin
   null;
end;
