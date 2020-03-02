------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                       N A M E D _ S E M A P H O R E S                    --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2019-2020, AdaCore                     --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that  it will be useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General Public License  distributed with  gnatprove;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with System;

package Named_Semaphores is

   --  (Quite) Thin Ada binding for named semaphores, that works on Linux and
   --  Windows. See also sem_overview(7) and the documentation of Semaphore
   --  Objects of Windows.

   --  The objective is to limit the access to some resource to at most N
   --  clients (e.g. processes). To this end, the user can create a semaphore
   --  with a fixed name using Create and the initial value N. This semaphore
   --  can then be opened additionally in other processes using the same fixed
   --  name.

   --  Whenever the processes want to access the resource, they call Wait. If
   --  the current value of the semaphore is greater than 0, Wait decrements
   --  this value and returns. After finishing with the resource, the processes
   --  call Release, which increments the value of the semaphore again.

   --  If upon calling Wait, the semaphore value is 0, the process waits (=
   --  Wait does not return) until it becomes non-zero. If several processes
   --  are waiting, only one will continue, chosen randomly.

   --  There is one difference between Linux and Windows for this
   --  implementation. On Linux, a named semaphore must be explicitly deleted
   --  using Delete. (However, the semaphore stays active until all processes
   --  have closed it). On Windows, the semaphore is destroyed automatically
   --  when all processes have closed it and a manual delete operation is not
   --  provided. If you want to achieve the same behavior on both systems, make
   --  sure that at least one process keeps the semaphore opened for as long as
   --  you need it, and call Delete at the end.

   type Semaphore is limited private;

   procedure Create (Name : String; Init : Natural; S : out Semaphore);
   --  Creates a semaphore with the given name and the initial value Init
   --  in the semaphore namespace. The semaphore can be used directly in the
   --  same process using Wait, Release or Close, or in it can be opened via
   --  Open in other processes.

   procedure Open (Name : String; S : out Semaphore);
   --  Open a semaphore that already has been created previously using Create

   procedure Close (S : in out Semaphore);
   --  Closes the handle on the semaphore

   procedure Wait (S : in out Semaphore);
   --  Block until the value of the semaphore is larger than 0, then decrease
   --  the value of the semaphore by 1 and return.

   procedure Release (S : in out Semaphore);
   --  Increase the value of the semaphore by 1

   procedure Delete (Name : String);
   --  Deletes the name of the semaphore from the semaphore namespace. The
   --  semaphore remains alive until all processes have closed it. This
   --  procedure is a no-op on Windows.

private

   type Semaphore is new System.Address;

end Named_Semaphores;
