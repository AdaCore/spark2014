pragma Ada_2012;
function After_Tax
  (Before_Tax : Natural;
   Rate       : Natural) return Natural
with
  Pre => (Rate <= 100),
  Post => (After_Tax'Result <= Before_Tax);
