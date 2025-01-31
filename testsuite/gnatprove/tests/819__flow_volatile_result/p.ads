package P is
   type T is new Integer with Volatile;
   function F return T is (0) with Volatile_Function;
end;
