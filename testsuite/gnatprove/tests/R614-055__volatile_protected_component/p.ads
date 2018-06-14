package P is

   type T is new Integer with Volatile;

   protected type PT is
      function F return Boolean;
   private
      C : T := 0;
   end;

end;
