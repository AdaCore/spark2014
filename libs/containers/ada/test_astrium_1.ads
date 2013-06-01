--  a list can be used to store the set of currently enabled monitoring of a
--  system. Then, we may wish to verify that if no monitoring detects failure,
--  then no recovery is triggered

with Common; use Common; use Common.DLL;

package Test_Astrium_1 is

   type Recovery_T  is (None, Reboot);

   function Test_Recovery (L : List) return Recovery_T
   with Post => (if (for all Cu in L => Detects_Failure (Element(Cu)) = False)
                 then Test_Recovery'Result = None);

end Test_Astrium_1;
