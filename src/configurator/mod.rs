// Copyright © 2020, Oracle and/or its affiliates.
//
// Copyright (c) 2019 Intel Corporation. All rights reserved.
// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

//! Traits and structs for configuring and loading boot parameters.
//! - [BootConfigurator](trait.BootConfigurator.html): configure boot parameters.
//! - [LinuxBootConfigurator](linux/struct.LinuxBootConfigurator.html): Linux boot protocol
//!   parameters configurator.
//! - [PvhBootConfigurator](pvh/struct.PvhBootConfigurator.html): PVH boot protocol parameters
//!   configurator.

use vm_memory::{ByteValued, GuestAddress, GuestMemory};

use std::error::Error as StdError;
use std::fmt;

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
mod x86_64;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub use x86_64::*;

#[cfg(target_arch = "aarch64")]
mod aarch64;
#[cfg(target_arch = "aarch64")]
pub use aarch64::*;

/// Errors specific to boot protocol configuration.
#[derive(Debug, PartialEq)]
pub enum Error {
    /// Errors specific to the Linux boot protocol configuration.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    Linux(linux::Error),
    /// Errors specific to the PVH boot protocol configuration.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    Pvh(pvh::Error),
    /// Errors specific to device tree boot configuration.
    #[cfg(target_arch = "aarch64")]
    Fdt(fdt::Error),
}

impl StdError for Error {
    fn description(&self) -> &str {
        use Error::*;
        match self {
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            Linux(ref e) => e.description(),
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            Pvh(ref e) => e.description(),
            #[cfg(target_arch = "aarch64")]
            Fdt(ref e) => e.description(),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Boot Configurator Error: {}",
            StdError::description(self)
        )
    }
}

/// A specialized `Result` type for the boot configurator.
pub type Result<T> = std::result::Result<T, Error>;

/// Trait that defines interfaces for building (TBD) and configuring boot parameters.
///
/// Currently, this trait exposes a single function which writes user-provided boot parameters into
/// guest memory at the user-specified addresses. It's meant to be called after the kernel is
/// loaded and after the boot parameters are built externally (in the VMM).
///
/// This trait will be extended with additional functionality to build boot parameters.
pub trait BootConfigurator {
    /// Writes the boot parameters (configured elsewhere) into guest memory.
    ///
    /// The arguments are split into `header` and `sections` to accommodate different boot
    /// protocols like Linux boot and PVH. In Linux boot, the e820 map could be considered as
    /// `sections`, but it's already encapsulated in the `boot_params` and thus all the boot
    /// parameters are passed through a single struct. In PVH, the memory map table is separated
    /// from the `hvm_start_info` struct, therefore it's passed separately.
    ///
    /// # Arguments
    ///
    /// * `params` - struct containing the header section of the boot parameters, additional
    ///              sections and modules, and their associated addresses in guest memory. These
    ///              vary with the boot protocol used.
    /// * `guest_memory` - guest's physical memory.
    fn write_bootparams<T, S, R, M>(params: BootParams<T, S, R>, guest_memory: &M) -> Result<()>
    where
        T: ByteValued,
        S: ByteValued,
        R: ByteValued,
        M: GuestMemory;
}

/// Header section of the boot parameters and associated guest memory address.
///
/// For the Linux boot protocol, it contains a [`boot_params`] struct and the zero page address.
/// For the PVH boot protocol, it contains a [`hvm_start_info`] struct and its address.
///
/// [`boot_params`]: ../loader/bootparam/struct.boot_params.html
/// [`hvm_start_info`]: ../loader/elf/start_info/struct.hvm_start_info.html
pub struct BootHeader<T: ByteValued> {
    /// Header section of the boot parameters.
    pub header: T,
    /// Address where it will be written in guest memory.
    pub address: GuestAddress,
}

/// Sections of the boot parameters and associated guest memory address.
///
/// Unused for the Linux boot protocol.
/// For the PVH boot protocol, they're used to specify both the memory map table in
/// [`hvm_memmap_table_entry`] structs, and, optionally, boot modules in [`hvm_modlist_entry`]
/// structs.
///
/// [`hvm_memmap_table_entry`]: ../loader/elf/start_info/struct.hvm_memmap_table_entry.html
/// [`hvm_modlist_entry`]: ../loader/elf/start_info/struct.hvm_modlist_entry.html
pub struct BootSections<T: ByteValued> {
    /// Data sections of the boot parameters.
    pub sections: Vec<T>,
    /// Address where they will be written in guest memory.
    pub address: GuestAddress,
}

/// Boot parameters to be written in guest memory.
pub struct BootParams<T: ByteValued, S: ByteValued, R: ByteValued> {
    /// "Header section", always written in guest memory irrespective of boot protocol.
    pub header: BootHeader<T>,
    /// Optional sections containing boot configurations (e.g. E820 map).
    pub sections: Option<BootSections<S>>,
    /// Optional modules specified at boot configuration time.
    pub modules: Option<BootSections<R>>,
}

impl<T, S, R> BootParams<T, S, R>
where
    T: ByteValued,
    S: ByteValued,
    R: ByteValued,
{
    /// Aggregates boot parameters into a [`BootParams`](struct.BootParams.html) struct.
    ///
    /// # Arguments
    ///
    /// * `header` - [`ByteValued`] representation of mandatory boot parameters.
    /// * `header_addr` - address in guest memory where `header` will be written.
    /// * `sections` - optional list of [`ByteValued`] boot configurations and associated address.
    /// * `modules` - optional list of [`ByteValued`] boot modules and associated address.
    ///
    /// [`ByteValued`]: https://docs.rs/vm-memory/latest/vm_memory/bytes/trait.ByteValued.html
    pub fn new(
        header: T,
        header_addr: GuestAddress,
        sections: Option<(Vec<S>, GuestAddress)>,
        modules: Option<(Vec<R>, GuestAddress)>,
    ) -> Self {
        Self {
            header: BootHeader {
                header,
                address: header_addr,
            },
            sections: if let Some((sections, address)) = sections {
                Some(BootSections { sections, address })
            } else {
                None
            },
            modules: if let Some((modules, address)) = modules {
                Some(BootSections {
                    sections: modules,
                    address,
                })
            } else {
                None
            },
        }
    }
}
