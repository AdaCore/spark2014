package P is
   Current_Mode : Integer;
   function No_Change return Boolean
   is (True)
   with Post =>
     (No_Change'Result = (Current_Mode = Current_Mode'Old));
end P;
