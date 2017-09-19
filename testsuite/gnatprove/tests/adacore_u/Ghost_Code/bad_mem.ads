package Bad_Mem is
   pragma Assertion_Policy (Ghost => Ignore, Pre => Check);

   procedure Alloc with
     Pre  => Free_Memory > 0,
     Post => Free_Memory < Free_Memory'Old;

   function Free_Memory return Natural with Ghost;

end Bad_Mem;
