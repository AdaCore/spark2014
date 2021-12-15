package Switch
--# own in State;
is

   type Reading is (on, off, unknown);

   function ReadValue return Reading;
   --# global in State;

end Switch;
