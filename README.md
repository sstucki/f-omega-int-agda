# ICFP 2021 Artifact

Name: **A theory of Higher-order Subtyping with Type Intervals**

Authors: Sandro Stucki and Paolo G. Giarrusso

## Artifact Instructions

Our virtual machine and source archives contain the extended version
of our [paper](icfp21-long.pdf), the Agda source code, and the source
pretty-printed into hyperlinked HTML for easy navigation. To browse
the latter, start from [html/Correspondence.html](html/Correspondence.html).

To build the artifact:
- `make doc` will typecheck the artifact and print it as hyper-linked HTML
  (results are cached);
- `make` will just typecheck the artifact but not generate HTML;
- `make clean` will remove the typechecking caches (`.agdai` files);
- `make cleanall` will perform `make clean` _and_ remove the generated HTML.


### If you are viewing the contents of our VM archive...

see the [QEmu Instructions](#qemu-instructions) below for how to setup,
start and connect to the VM.

Log into the VM as the user `artifact`, e.g. by running `ssh -p 5555
artifact@localhost` and using the password `password`.  Once you are
logged into the VM, you can change to the `artifact` directory and
check the Agda mechanization by running

    cd artifact
    make

This will typecheck the [Correspondence.agda](src/Correspondence.agda)
file in the `src` directory which imports the Agda modules containing
mechanized versions of the main definitions, lemmas and theorems described
in the paper.

For suggestions on how to navigate the source code, see [How to navigate
the Agda mechanization below](#how-to-navigate-the-agda-mechanization).


### If you are viewing the contents of the source tarball...

you will need to install Agda 2.6.2 and version 1.7 of the Agda
standard library.  The code in this archive has been verified using
this setup and type checks without errors or warnings (using the
default `-Wwarn` setting).  Newer versions of Agda and its standard
library may also work, though some warnings or minor errors are to be
expected since neither Agda nor its standard library guarantee
backwards compatibility with earlier versions.

The Agda distribution and standard library, along with setup
instructions, can be found at

 * https://github.com/agda/agda
 * https://github.com/agda/agda-stdlib

Once you have Agda installed, the easiest way to check the mechanization is
to unpack the archive, enter the `artifact/` directory and run

    make

which will typecheck the [Correspondence.agda](src/Correspondence.agda)
file in the `src` directory.  This file imports the Agda modules containing
mechanized versions of the main definitions, lemmas and theorems described
in the paper.

Alternatively, if you are a GNU/Emacs user, you can open the
[src/Correspondence.agda](src/Correspondence.agda) file using the [Agda
Emacs mode](https://github.com/agda/agda#configuring-the-emacs-mode) and
type `C-c C-l`.

See the next section for suggestions on how to navigate the source code.


### How to navigate the Agda mechanization

To simplify the comparison between the metatheoretic results described in
the paper and the corresponding Agda mechanization, we include a file
[Correspondence.agda](src/Correspondence.agda) in the `src` directory.  The
file lists the main results from the paper and imports the Agda modules
containing the relevant definitions and proofs.  For your convenience, we
have included a hyper-linked and syntax-highlighted HTML version of this
file (and all other source files relevant to the mechanization) in the
`html` directory: [html/Correspondence.html](html/Correspondence.html).  To
explore a particular definition or proof, just click on the corresponding
Agda module or definition in the HTML version of the source code.

An exhaustive list of all the modules contained in the mechanization with a
brief description is contained in the [src/README.agda](src/README.agda)
([HTML version](html/README.html)) file, and in the [appendix of our
paper](icfp21-long.pdf).


## QEmu Instructions

The ICFP 2021 Artifact Evaluation Process is using a Debian QEmu image as a
base for artifacts. The Artifact Evaluation Committee (AEC) will verify that
this image works on their own machines before distributing it to authors.
Authors are encouraged to extend the provided image instead of creating their
own. If it is not practical for authors to use the provided image then please
contact the AEC co-chairs before submission.

QEmu is a hosted virtual machine monitor that can emulate a host processor
via dynamic binary translation. On common host platforms QEmu can also use
a host provided virtualization layer, which is faster than dynamic binary
translation.

QEmu homepage: https://www.qemu.org/

### Installation

#### OSX
``brew install qemu``

#### Debian and Ubuntu Linux
``apt-get install qemu-kvm``

On x86 laptops and server machines you may need to enable the
"Intel Virtualization Technology" setting in your BIOS, as some manufacturers
leave this disabled by default. See Debugging.md for details.


#### Arch Linux

``pacman -Sy qemu``

See https://wiki.archlinux.org/index.php/QEMU for more info.

See Debugging.md if you have problems logging into the artifact via SSH.


#### Windows 10
Download and install QEmu via the links on https://www.qemu.org/download/#windows.
Ensure that qemu-system-x86_64.exe is in your path.
Start Bar -> Search -> "Windows Features"
          -> enable "Hyper-V" and "Windows Hypervisor Platform".
Restart your computer.

#### Windows 8

See Debugging.md for Windows 8 install instructions.



### Startup

The base artifact provides a `start.sh` script to start the VM on unix-like
systems and `start.bat` for Windows. Running this script will open a graphical
console on the host machine, and create a virtualized network interface.
On Linux you may need to run with 'sudo' to start the VM. If the VM does not
start then check `Debugging.md`

Once the VM has started you can login to the guest system from the host using:

```
$ ssh -p 5555 artifact@localhost             (password is 'password')
```

You can also copy files to and from the host using scp, eg:

```
$ scp -P 5555 artifact@localhost:somefile .  (password is 'password')
```

The root account password is ``password``.

The default user is username:```artifact``` password:```password```.


### Shutdown

To shutdown the guest system cleanly, login to it via ssh and use:

```
$ sudo shutdown now
```


### Artifact Preparation

Authors should install software dependencies into the VM image as needed,
preferably via the standard Debian package manager. For example, to install
GHC and cabal-install, login to the host and type:

```
$ sudo apt update
$ sudo apt install ghc
$ sudo apt install cabal-install
```

If you really need a GUI then you can install X as follows, but we prefer
console-only artifacts whenever possible.

```
$ sudo apt-get install xorg
$ sudo apt-get install xfce4   # or some other window manager
$ startx
```

See Debugging.md for advice on resolving other potential problems,
particularly when installing the current version of Coq via opam.

If your artifact needs lots of memory you may need to increase the value
of the ```QEMU_MEM_MB``` variable in the ```start.sh``` script.

When preparing your artifact, please also follow the guidelines at:
 https://icfp21.sigplan.org/track/icfp-2021-artifact-evaluation#Forms-of-Artifacts

------------------------------------------------------------------------
Copyright (c) 2021 Sandro Stucki, Paolo G. Giarrusso
