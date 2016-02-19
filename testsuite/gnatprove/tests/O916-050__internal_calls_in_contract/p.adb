package body P is

   protected body PT is
      function Internal return Boolean is (True);
      procedure Proc1 is begin null; end;
      procedure Proc2 is begin null; end;
      function Foo return Boolean is (False);
   end;

end;
