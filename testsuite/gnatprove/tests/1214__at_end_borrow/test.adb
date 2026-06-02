procedure Test with SPARK_Mode is

   function At_End_1 (X : access Integer) return access Integer with
     Ghost,
     Import,
     Annotate => (GNATprove, At_End_Borrow);

   function At_End_2 (X : access Integer) return access Integer with
     Ghost,
     Annotate => (GNATprove, At_End_Borrow);
   function At_End_2 (X : access Integer) return access Integer
     with SPARK_Mode => Off
   is
   begin
      return X;
   end At_End_2;

begin
   null;
end;
