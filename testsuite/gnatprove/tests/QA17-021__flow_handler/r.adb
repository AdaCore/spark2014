package body R is

   protected body PT is
      procedure Foo is
      begin
         X := not X;
      end;
   end;

end;
