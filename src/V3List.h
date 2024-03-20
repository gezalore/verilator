// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Doubly linked endogenous (intrusive) list
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3LIST_H_
#define VERILATOR_V3LIST_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"

#include <type_traits>
#include <utility>

//============================================================================
// The list links (just 2 pointers), to be instantiated as a member in the
// list element base class 'T_Base'. They are considered mutable, even if the
// list element is 'const', as they are only used for storing the elements in
// a V3List. That is, you can store const elements in a V3List.
template <typename T_Base>
class V3ListLinks final {
    // The V3List itself, but nothing else can access the link pointers
    template <typename B, V3ListLinks<B> B::*, typename>
    friend class V3List;

    T_Base* m_nextp = nullptr;  // Next element in list
    T_Base* m_prevp = nullptr;  // Previous element in list

public:
    V3ListLinks() = default;
    ~V3ListLinks() {
#ifdef VL_DEBUG
        m_nextp = reinterpret_cast<T_Base*>(1);
        m_prevp = reinterpret_cast<T_Base*>(1);
#endif
    }
    VL_UNCOPYABLE(V3ListLinks);
    VL_UNMOVABLE(V3ListLinks);
};

//============================================================================
// Generic endogenous (or intrusive) doubly linked list, with links stored
// inside the elements. The template parameters are:
// - 'T_Base' is the base type of elements that contains the V3ListLinks
//   instance as a data member.
// - 'LinksPointer' is a member pointer to the links within 'T_Base'
// - 'T_Element' is the actual type of elements, which must be the same,
//    or a subtype of 'T_Base'.
template <typename T_Base, V3ListLinks<T_Base> T_Base::*LinksPointer, typename T_Element = T_Base>
class V3List final {
    static_assert(std::is_base_of<T_Base, T_Element>::value,
                  "'T_Element' must be a subtype of 'T_Base");
    T_Base* m_headp = nullptr;
    T_Base* m_lastp = nullptr;

    // Given the T_Element, return the Links. The links are always mutable, even in const elements.
    VL_ATTR_ALWINLINE
    static V3ListLinks<T_Base>& toLinks(const T_Base& element) {
        return const_cast<T_Base&>(element).*LinksPointer;
    }

    // Iterator class template for V3List. This is just enough to support range based for loops
    // and basic usage. Feel free to extend as required.
    template <typename IteratorElement>
    class SimpleItertatorImpl final {
        static_assert(std::is_same<IteratorElement, T_Element>::value
                          || std::is_same<IteratorElement, const T_Element>::value,
                      "'ItertatorImpl' must be used with element type only");

        // The List itself, but nothing else can construct iterators
        template <typename B, V3ListLinks<B> B::*P, typename>
        friend class V3List;

        using SelfType = SimpleItertatorImpl<IteratorElement>;

        T_Base* m_currp;  // Currently iterated element, or 'nullptr' for 'end()'

        SimpleItertatorImpl(T_Base* elementp)
            : m_currp{elementp} {
            VL_PREFETCH_RW(elementp);
        }
        SimpleItertatorImpl(std::nullptr_t)
            : m_currp{nullptr} {}

    public:
        // Dereference
        VL_ATTR_ALWINLINE
        IteratorElement& operator*() const {
            UDEBUGONLY(UASSERT(m_currp, "Dereferencing end of list iterator"););
            return *static_cast<IteratorElement*>(m_currp);
        }
        // Pre increment
        VL_ATTR_ALWINLINE
        SelfType& operator++() {
            UDEBUGONLY(UASSERT(m_currp, "Pre-incrementing end of list iterator"););
            m_currp = toLinks(*m_currp).m_nextp;
            if (VL_LIKELY(m_currp)) VL_PREFETCH_RW(m_currp);
            return *this;
        }
        // Post increment
        VL_ATTR_ALWINLINE
        SelfType operator++(int) {
            UDEBUGONLY(UASSERT(m_currp, "Post-incrementing end of list iterator"););
            T_Base* const elementp = m_currp;
            m_currp = toLinks(*m_currp).m_nextp;
            if (VL_LIKELY(m_currp)) VL_PREFETCH_RW(m_currp);
            return SelfType{elementp};
        }
        VL_ATTR_ALWINLINE
        bool operator==(const SelfType& other) const { return m_currp == other.m_currp; }
        VL_ATTR_ALWINLINE
        bool operator!=(const SelfType& other) const { return m_currp != other.m_currp; }
        // Convert to const iterator
        VL_ATTR_ALWINLINE
        operator SimpleItertatorImpl<const IteratorElement>() const {
            return SimpleItertatorImpl<const IteratorElement>{m_currp};
        }
    };

public:
    using SelfType = V3List<T_Base, LinksPointer, T_Element>;
    using iterator = SimpleItertatorImpl<T_Element>;
    using const_iterator = SimpleItertatorImpl<const T_Element>;

    V3List() = default;
    ~V3List() {
#ifdef VL_DEBUG
        m_headp = reinterpret_cast<T_Element*>(1);
        m_lastp = reinterpret_cast<T_Element*>(1);
#endif
    }
    VL_UNCOPYABLE(V3List);
    VL_UNMOVABLE(V3List);

    bool empty() const {
        UDEBUGONLY(UASSERT(!m_headp == !m_lastp, "Inconsistent list"););
        return !m_headp;
    }

    bool hasSingleElement() const {
        UDEBUGONLY(UASSERT(!m_headp == !m_lastp, "Inconsistent list"););
        return m_headp && m_headp == m_lastp;
    }

    bool hasMultipleElements() const {
        UDEBUGONLY(UASSERT(!m_headp == !m_lastp, "Inconsistent list"););
        return m_headp && m_headp != m_lastp;
    }

    T_Element* frontp() { return static_cast<T_Element*>(m_headp); }
    const T_Element* frontp() const { return static_cast<T_Element*>(m_headp); }
    T_Element* backp() { return static_cast<T_Element*>(m_lastp); }
    const T_Element* backp() const { return static_cast<T_Element*>(m_lastp); }

    //    T_Element& front() {
    //        UASSERT(!empty(), "'front' called on empty list");
    //        return *static_cast<T_Element*>(m_headp);
    //    }
    //    const T_Element& front() const {
    //        UASSERT(!empty(), "'front' called on empty list");
    //        return *static_cast<T_Element*>(m_headp);
    //    }
    //    T_Element& back() {
    //        UASSERT(!empty(), "'back' called on empty list");
    //        return *static_cast<T_Element*>(m_lastp);
    //    }
    //    const T_Element& back() const {
    //        UASSERT(!empty(), "'back' called on empty list");
    //        return *static_cast<T_Element*>(m_lastp);
    //    }

    iterator begin() { return iterator{m_headp}; }
    const_iterator begin() const { return const_iterator{m_headp}; }
    iterator end() { return iterator{nullptr}; }
    const_iterator end() const { return const_iterator{nullptr}; }

    void push_back(const T_Element& element) {
        auto& links = toLinks(element);
        links.m_nextp = nullptr;
        links.m_prevp = m_lastp;
        if (m_lastp) toLinks(*m_lastp).m_nextp = &const_cast<T_Element&>(element);
        m_lastp = &const_cast<T_Element&>(element);
        if (!m_headp) m_headp = m_lastp;
    }

    T_Element* unlinkBack() {
        T_Element* const lastp = m_lastp;
        if (lastp) {
            m_lastp = toLinks(*m_lastp).m_prevp;
            if (m_lastp) {
                toLinks(*m_lastp).m_nextp = nullptr;
            } else {
                m_headp = nullptr;
            }
        }
        return lastp;
    }

    void push_front(const T_Element& element) {
        auto& links = toLinks(element);
        links.m_nextp = m_headp;
        links.m_prevp = nullptr;
        if (m_headp) toLinks(*m_headp).m_prevp = &const_cast<T_Element&>(element);
        m_headp = &const_cast<T_Element&>(element);
        if (!m_lastp) m_lastp = m_headp;
    }

    T_Element* unlinkFront() {
        T_Element* const headp = m_headp;
        if (headp) {
            m_headp = static_cast<T_Element*>(toLinks(*m_headp).m_nextp);
            if (m_headp) {
                toLinks(*m_headp).m_prevp = nullptr;
            } else {
                m_lastp = nullptr;
            }
        }
        return headp;
    }

    void erase(const T_Element& element) {
        auto& links = toLinks(element);
        if (links.m_nextp) toLinks(*links.m_nextp).m_prevp = links.m_prevp;
        if (links.m_prevp) toLinks(*links.m_prevp).m_nextp = links.m_nextp;
        if (m_headp == &element) m_headp = links.m_nextp;
        if (m_lastp == &element) m_lastp = links.m_prevp;
        links.m_prevp = nullptr;
        links.m_nextp = nullptr;
    }

    void swap(SelfType& other) {
        std::swap(m_headp, other.m_headp);
        std::swap(m_lastp, other.m_lastp);
    }

    void splice(const_iterator pos, SelfType& other) {
        if (empty()) {
            swap(other);
        } else if (other.empty()) {
            return;
        } else {
            UASSERT(pos == end(), "Sorry, only splicing at the end is implemented at the moment");
            toLinks(*m_lastp).m_nextp = other.m_headp;
            toLinks(*other.m_headp).m_prevp = m_lastp;
            m_lastp = other.m_lastp;
            other.m_headp = nullptr;
            other.m_lastp = nullptr;
        }
    }
};

#endif  // Guard
