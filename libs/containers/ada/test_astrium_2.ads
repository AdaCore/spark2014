--  we may wish to verify that if some monitoring detects failure, then the
--  recovery with the highest priority is triggered

with Common; use Common; use Common.OS;

package Test_Astrium_2 is

   function Test_Recovery_Highest (S : Set) return Recovery
   with Pre  => not Is_Empty(S),
        Post => (for all Cu in S => True);
--                   not (Test_Recovery_Highest'Result < Element(Cu)));

end Test_Astrium_2;
