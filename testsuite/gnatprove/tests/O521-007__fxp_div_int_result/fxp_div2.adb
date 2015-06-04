procedure Fxp_div2 is

   type Duration_Rep is range -(2 ** 63) .. +((2 ** 63 - 1));
   for Duration_Rep'Size use 64;

   X : Duration;

   Y : constant Duration_Rep := Duration_Rep (X / X);
   Z : constant Duration_Rep := Duration_Rep (X / Duration (Duration'Small + Duration'Small));

begin
   null;
end Fxp_div2;
