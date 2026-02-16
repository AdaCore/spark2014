package body Example is
   protected body Foo is
      entry Wait when Wait'Count > 2 is
      begin
         null;
      end Wait;
   end Foo;
end Example;
