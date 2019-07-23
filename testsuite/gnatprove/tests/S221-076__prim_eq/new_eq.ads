package New_Eq with SPARK_Mode is
   type T is private with Default_Initial_Condition;
   function My_prop (X, Y : T) return Boolean;
   function "=" (X, Y : T) return Boolean with
     Post => (if "="'result then My_prop (X, Y));
private
   pragma SPARK_Mode (Off);
   type T is null record;
end New_Eq;
