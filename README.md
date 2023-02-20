<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# FlocqLecture

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/thery/FlocqLecture/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/thery/FlocqLecture/actions?query=workflow:"Docker%20CI"




This is an introductory course **Floating-Point Numbers and Formal Proof**
given at [ENS Lyon](http://www.ens-lyon.fr/LIP/) in 2016-2017.
It is based on the [Flocq Library](http://flocq.gforge.inria.fr/). 

----
It is composed of four lectures:

1. [Real numbers](./lecture1.v) ([solution](./lecture1_solution.v))
2. [Rounding](./lecture2.v) ([solution](./lecture2_solution.v))
3. [Proof I](./lecture3.v) ([solution](./lecture3_solution.v))
4. [Proof II](./lecture3.v) ([solution](./lecture4_solution.v))

----
Laurent Théry (Laurent.Thery@inria.fr)

## Meta

- Author(s):
  - Laurent Théry
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.16 or later
- Additional dependencies:
  - [Flocq 4.1 or later](https://gitlab.inria.fr/flocq/flocq.git)
- Coq namespace: `FlocqLecture`
- Related publication(s): none

## Building and installation instructions

To build and install manually, do:

``` shell
git clone https://github.com/thery/FlocqLecture.git
cd FlocqLecture
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



