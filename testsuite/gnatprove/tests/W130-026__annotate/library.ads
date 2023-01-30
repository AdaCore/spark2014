package Library is

   pragma Warnings (Off);
   function At_End (A : access constant Boolean)
                    return access constant Boolean
   is (A)
     with Ghost;
   pragma Warnings (On);
   pragma Annotate (GNATprove, At_End_Borrow, At_End);

end Library;
