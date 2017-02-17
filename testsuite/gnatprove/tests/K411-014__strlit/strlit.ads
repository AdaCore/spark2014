package Strlit is

   type Five is new String(1..5);
   function DoSome return Integer
      with Post => (DoSome'Result = 10);
end Strlit;
