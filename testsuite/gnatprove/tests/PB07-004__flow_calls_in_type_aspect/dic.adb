package body Dic is

   protected body PT is
      procedure Dummy is
         X : T := 0;      -- evaluation of type predicate calls Yield
      begin
         null;
      end;
   end;

end;
