package Hidden_Dispatch with SPARK_Mode is
   type T is private;
   function F (X : T) return Boolean;
   procedure P1 (X : in out T) with
     Pre => F (X);
   procedure P2 (X : not null access T) with
     Pre => F (X.all);
private
   type T is tagged record
      F : Integer;
   end record;
end Hidden_Dispatch;
