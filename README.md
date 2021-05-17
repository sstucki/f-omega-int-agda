# ICFP 2021 Artifact

Name: **A theory of Higher-order Subtyping with Type Intervals**

## Artifact Instructions

**[Authors should add their own instructions here about how to exercise their
   artifact. Authors can either fold the QEmu instructions below into this
   section, or leave the QEmu section in place at the bottom.]**

Our virtual machine and package contain the paper (and appendix), the Agda source code,
and the source pretty-printed into hyperlinked HTML for easy navigation. To
browse the latter, start from (FIXME check)
[html/Correspondence.agda](html/Correspondence.agda).

To build the artifact:
- `make doc` will typecheck the artifact and print it as hyper-linked HTML; results are cached
- `make` will typecheck the artifact; results are cached
- `make clean` will remove the typechecking caches (`.agdai` files)
- `make cleanall` will perform `make clean` _and_ remove the generated HTML.

_**FIXME:** stub copied from the README.md in the `master` branch._

A mechanized type safety proof for Fω extended with interval kinds.

The code in this repository contains an Agda mechanization of the type system Fω extended with *interval kinds* ("F omega int").  An interval kind `A..B` represents a type interval bounded by a pair of types `A`, `B`.  It is inhabited by all proper types `C : A..B` that are both supertypes of `A` and subtypes of `B`.  Interval kinds are flexible enough to express various features found in other type systems, such as

 * F-<:-style bounded polymorphism,
 * bounded type operators,
 * singleton kinds and first-class type definitions.

The mechanization includes a small-step operational call-by-value semantics, declarative and canonical presentations of typing and kinding, along with (syntactic) proofs of various meta-theoretic properties, such as

 * weak normalization of types (and kinds) via hereditary substitution,
 * subject reduction for types (w.r.t. full β-reduction),
 * type safety (progress & preservation) w.r.t. to the CBV semantics,
 * undecidability of subtyping.


### The Agda mechanization

The file `src/README.agda` contains a detailed overview of the formalization.

The theory has been mechanized in [Agda](https://github.com/agda/agda) and makes heavy use of the [Agda standard library](https://github.com/agda/agda-stdlib).  The code in this repository has been type-checked using Agda 2.6.1.3 and version 1.6 of the Agda standard library.  The latest versions of the Agda distribution and standard library, along with setup instructions, can be found at

 * https://github.com/agda/agda
 * https://github.com/agda/agda-stdlib

The easiest way to check all the code is to compile the `README.agda` file from the `src/` directory.  Run

    agda src/README.agda

in the console, or simply open the file using the [Agda Emacs mode](https://github.com/agda/agda#configuring-the-emacs-mode) and type `C-c C-l`.

### License

The source code is released under the MIT License.  See the `LICENSE` file for details.

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

