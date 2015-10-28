with Zero;
pragma Elaborate_All (Zero);

package P is

   task type Timer (Countdown : Natural)
   is
      pragma Priority (Countdown);
   end;

   T : Timer (10 / Zero);

end;
