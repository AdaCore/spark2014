package P is

   type T is limited private;

private

   function Zero return Integer is (0);

   task type T is
      pragma Priority (1 / Zero);
   end;

end;
